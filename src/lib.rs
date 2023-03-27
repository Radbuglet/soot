#![cfg_attr(not(test), no_std)]

#[doc(hidden)]
pub mod macro_internals {
    use core::{
        cell::RefCell,
        future::Future,
        iter,
        marker::PhantomData,
        mem::{transmute, ManuallyDrop, MaybeUninit},
        pin::Pin,
        ptr,
        task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
    };

    /// Re-exports for [`self_ref!`](crate::self_ref).
    pub mod re_export {
        pub use core::{
            future::{pending, Future},
            option::Option::{None, Some},
        };
    }

    /// Constructs a dummy waker that does nothing.
    fn dummy_waker() -> ManuallyDrop<Waker> {
        const VTABLE: RawWakerVTable = RawWakerVTable::new(
            |data| RawWaker::new(data, &VTABLE),
            |_data| {},
            |_data| {},
            |_data| {},
        );

        ManuallyDrop::new(unsafe { Waker::from_raw(RawWaker::new(ptr::null(), &VTABLE)) })
    }

    /// Fetches the output type of a [`SelfRefOutput`] given the lifetime `'a`.
    type Feed<'a, T> = <T as SelfRefOutput<'a>>::Output;

    /// Fetches the output type of a [`SelfRefIterOutput`] given the lifetime `'a`.
    type FeedIter<'a, T> = <T as SelfRefIterOutput<'a>>::IterOutput;

    /// A trait used to indicate the return type of a [`SelfRef`] given a future lifetime `'a`.
    ///
    /// This trait should not be implemented on structures manually but rather referenced as:
    /// ```ignore
    /// type MyOutputCollection = dyn for<'a> SelfRefOutput<'a, Output = &'a u32>;
    /// ```
    pub trait SelfRefOutput<'a> {
        type Output; // FIXME: Should this be `'a`?
    }

    /// A trait used to indicate the return type of a [`SelfRef`] being used as an iterator given a
    /// future lifetime `'a`. Everything that implements [`SelfRefIterOutput`] also implements
    /// [`SelfRefOutput`] with an output of `Option<IterOutput>`.
    ///
    /// See [`SelfRefOutput`] documentation for how to use this trait.
    pub trait SelfRefIterOutput<'a> {
        type IterOutput;
    }

    impl<'a, T: ?Sized + SelfRefIterOutput<'a>> SelfRefOutput<'a> for T {
        type Output = Option<T::IterOutput>;
    }

    /// A new-type wrapper around a future producing self-referential data. This is constructed
    /// safely using the [`self_ref!`](crate::self_ref) macro.
    ///
    /// `T` represents the [`dyn for<'a> SelfRefOutput<'a, Output = ...>`](SelfRefOutput) instance
    /// describing the collection of values this [`SelfRef`] can produce.
    ///
    /// `F` represents the [`Future`] being used to produce these values.
    pub struct SelfRef<T: ?Sized, F> {
        _ty: PhantomData<fn(T) -> T>,
        future: RefCell<F>,
    }

    impl<T, F> SelfRef<T, F>
    where
        T: ?Sized + for<'a> SelfRefOutput<'a>,
        F: Future<Output = ()>,
    {
        /// Calls a generator closure immediately to produce the future wrapped by [`SelfRef`]. This
        /// future (the closure body assuming it's all `async`), however, will not process until the
        /// first call to [`SelfRef::get`] and similar.
        #[inline(always)]
        pub fn new<G>(generator: G) -> Self
        where
            G: FnOnce(SelfRefProvider<T>) -> F,
        {
            Self {
                _ty: PhantomData,
                future: RefCell::new(generator(SelfRefProvider { _ty: PhantomData })),
            }
        }

        #[inline(always)]
        pub fn get_streaming<'a>(self: Pin<&'a Self>) -> Feed<'a, T> {
            // N.B. we use a `RefCell` here because someone could technically call this function
            // recursively, although they'd have considerable difficulty doing so.
            let future = &mut *self.future.borrow_mut();
            let future = unsafe {
                // Safety: If `F: !Unpin`, then a `Pin` wrapper around a reference guarantees that
                // our structure, will not be moved. Because we never give out mutable references to
                // our future to anyone else, the future will also stay put. Huzzah for structural
                // pinning!
                Pin::new_unchecked(future)
            };

            // Construct a waker surrounded by a `SelfRefProviderFuture`. We do this to setup the
            // invariant that our `context`'s waker is always secretly a pointer to one of these.
            //
            // Details on why that invariant can be upheld are described below.
            let dummy_waker = SelfRefProviderFuture::<Feed<'a, T>> {
                waker: dummy_waker(),
                output: None,
                should_wake: false,
            };

            let mut context = Context::from_waker(&dummy_waker.waker);

            // Poll the future to give it a chance to update the waker.
            let _ = future.poll(&mut context);

            // Extract the `SelfRefProviderFuture` from the `context`'s current `waker`.
            let SelfRefProviderFuture { output, .. } = unsafe {
                // Safety: here's where things get tricky!
                //
                // 1.   First, why can we assume that our `Waker` is secretly a pointer to a
                //      `SelfRefProviderFuture<U>` for *some* `U`? We already know that the original
                //      waker starts out as the first field of a `SelfRefProviderFuture`, which is
                //      `repr(C)`. Additionally, is is `unsafe` and unsound for general executors for
                //      someone to mutate a `Context` instance and its associated waker. First,
                //      `Context` only gives getters to these `Waker` references—not setters. Second,
                //      and more importantly, although `Future`s get mutable references to a
                //      `Context<'_>`, the context object is invariant w.r.t `'_` and `'_` is
                //      existential. Since they only receive one context object with that existential
                //      lifetime, they cannot safely mutate the context. Thus, only an unsafe context
                //      with a sufficient number of guarantees about its executor could replace our
                //      waker—that context being `SelfRefProviderFuture::poll()`.
                //
                //      TODO: This logic relies on some unstable guarantees of the standard library.
                //        We currently protect against a breaking of the second guarantee with a
                //        doc-test (TODO: actually do this) but there's no real way to ensure that
                //        the standard library never adds a setter for the waker or defines some
                //        known layout which could be mutated. Luckily, these scenarios are somewhat
                //        theoretical, pretty unlikely to happen accidentally, and will almost surely
                //        happen *after* `waker_getters` (#96992) get stabilized.
                //
                // 2.   Next, how do we ensure that the `U` in `SelfRefProviderFuture<U>` is assignable
                //      to `Feed<'a, T>`? Three safety guarantees of `SelfRefProvider::provide()`
                //      make this possible.
                //
                // 2.1. First, `SelfRefProvider::<T>::provide()`—the only constructor for
                //      `SelfRefProviderFuture<Feed<'a, T>>`—requires callers to guarantee that they
                //      are executing the future in an `async` block immediately passed to a
                //      `SelfRef<T, _>` of the same type `T`. Therefore, our waker is pointing to
                //      `SelfRefProvider<Feed<'b, T>>` for some lifetime `'b`.
                //
                // 2.2. Second, `SelfRefProvider::<T>::provide()` requires callers to guarantee that
                //      `Feed<'c, T>` is covariant w.r.t `'c`. See [`SelfRefProvider::check_covariance`]
                //      and the expanded output of `crate::self_ref!` for details on how this proof
                //      is automated.
                //
                // 2.3. Third, `SelfRefProvider::<T>::provide()` requires callers to guarantee that
                //      the lifetime `'b` for which it is being called is only terminated once the
                //      future is dropped. Because `'a` is strictly less than that (the future can
                //      only be dropped if its wrapping `SelfRef` is dropped, which would force `'a`
                //      to expire), we know that `'b: 'a` and, by the covariance of `Feed<'c, T>`
                //      established prior, we know that `SelfRefProvider<Feed<'b, T>>` is assignable
                //      to our `SelfRefProvider<Feed<'a, T>>`, as expected.
                //
                // 3.   TODO: Justify why this type of C-style structure embedding is valid in Rust—
                //       even with obnoxious pointer-reference round-tripping. (right now, my only
                //       source of confidence for this operation is the fact that Miri with
                //       `MIRIFLAGS=-Zmiri-tree-borrows` environment variables accepts this routine)
                //
                // 4.   We keep this reference to our waker for at most the lifetime of our `context`
                //      object so there are no UAFs to be found here!
                //
                // Huzzah!
                &*(context.waker() as *const Waker as *const SelfRefProviderFuture<Feed<'a, T>>)
            };

            // Extract the output value from the waker.
            //
            // N.B. We will never leak with an initialized `MaybeUninit` because nothing can panic
            // in between the `Pending` resolution of our `SelfRefProviderFuture` and this line because
            // safe executions of `SelfRefProviderFuture` are expected to yield directly to the `future`
            // we're executing right now. If this line panics, it will only do so if the option
            // containing that `MaybeUninit` is `None`, which certainly cannot leak anything.
            let output = output.as_ref().expect(
                "`SelfRef` provider never provided a value. Was there an unexpected early \
                 return or an excess of reads?",
            );

            unsafe {
                // Safety: As a final internal invariant, we know that the `SelfRefProviderFuture`
                // will only set itself as the waker once. After that, it resolves and lets the next
                // future handle things.
                output.assume_init_read()
            }
        }

        #[inline(always)]
        pub fn get<'a>(self: Pin<&'a mut Self>) -> Feed<'a, T> {
            self.into_ref().get_streaming()
        }
    }

    impl<T, F> SelfRef<T, F>
    where
        T: ?Sized + for<'a> SelfRefIterOutput<'a>,
        F: Future<Output = ()>,
    {
        #[inline(always)]
        pub fn iter_streaming<'a>(
            self: Pin<&'a Self>,
        ) -> impl Iterator<Item = FeedIter<'a, T>> + 'a {
            iter::from_fn(move || self.get_streaming())
        }

        #[inline(always)]
        pub fn iter<'a>(self: Pin<&'a mut Self>) -> impl Iterator<Item = FeedIter<'a, T>> + 'a {
            self.into_ref().iter_streaming()
        }
    }

    /// A helper structure providing access to [`SelfRefOutput`] variance checking and type-safe
    /// [`provide`](SelfRefProvider::provide) calls.
    pub struct SelfRefProvider<T: ?Sized> {
        _ty: PhantomData<fn(T) -> T>,
    }

    impl<T: ?Sized + for<'a> SelfRefOutput<'a>> SelfRefProvider<T> {
        /// Returns a [`Future`] whose completion provides the given `output` to the calling [`SelfRef`].
        ///
        /// ## Safety
        ///
        /// 1. This may only be called and `.await`'ed upon directly in the `async` closure owned by
        ///    the correspondingly-typed `SelfRef<T, _>`.
        ///
        /// 2. `Feed<'a, T>` must be covariant w.r.t `'a`.
        ///
        /// 3. The lifetime `'_` for the `output: Feed<'_, T>` argument must not expire before the
        ///    async block in which this future is being `.await`ed is dropped.
        ///
        #[inline(always)]
        pub async unsafe fn provide(&self, output: Feed<'_, T>) {
            SelfRefProviderFuture::<Feed<'_, T>> {
                waker: dummy_waker(),
                output: Some(MaybeUninit::new(output)),
                should_wake: false,
            }
            .await;
        }

        /// A helper method to ensure that our specific `Feed<'a, T>` is covariant w.r.t `'a`.
        ///
        /// If an identity conversion of the form:
        ///
        /// ```ignore
        /// provider.check_covariance(|_, x| x);
        /// ```
        ///
        /// ...type checks, this implies that `Feed<'a, T>` is covariant.
        pub fn check_covariance(
            &self,
            // This trick was found courtesy of `Yandros`
            // Github: https://github.com/danielhenrymantilla
            _: impl for<'l, 's> FnOnce(
                // This is used to introduce the implication that `'l: 's`.
                [&'s &'l (); 0],
                // The double pointer indirection ensures that implicit unsizing and type promotion
                // conversions do not occur.
                *const *const Feed<'l, T>,
            ) -> *const *const Feed<'s, T>,
        ) {
            // (no-op)
        }
    }

    #[repr(C)]
    struct SelfRefProviderFuture<T> {
        waker: ManuallyDrop<Waker>,
        output: Option<MaybeUninit<T>>,
        should_wake: bool,
    }

    impl<T> Unpin for SelfRefProviderFuture<T> {}

    impl<T> Future for SelfRefProviderFuture<T> {
        type Output = ();

        #[inline(always)]
        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            let me = self.get_mut();

            if me.should_wake {
                Poll::Ready(())
            } else {
                me.should_wake = true;
                *cx = unsafe {
                    // Safety: From the safety guarantees `SelfRefProvider::provide()`—the only
                    // constructor of this future—we know that we are executing directly in an
                    // async block owned by an appropriate `SelfRef` wrapper.
                    //
                    // This is a transmute from a `Context` to a waker with a lifetime of `dummy_waker`
                    // in `SelfRef::get_streaming()` to a waker with a lifetime of the future being
                    // executed from when `future.poll()` terminates to the next `future.poll()` call.
                    // Hence, we are assigning from a `Context<'a>` to a `Context<'b>` where `'a: 'b`.
                    //
                    // Although `Context<'a>` is not technically covariant w.r.t `'a`, this is only
                    // for future proofing purposes and the structure cannot obtain another
                    // lifetime-limiting field without an intermediate call to some other setter
                    // we know neither this method—nor the de-sugared async block—will realistically
                    // make.
                    //
                    // TODO: This last paragraph is also speculation.
                    transmute(Context::from_waker(&me.waker))
                };
                Poll::Pending
            }
        }
    }
}

#[macro_export]
macro_rules! self_ref {
    // === Iterator variants === //
    (use iter $provided:ident in { $($rest:tt)* }) => {
        $crate::macro_internals::SelfRef::new(|provider| async move {
            provider.check_covariance(|_, x| x);
            $($rest)*
            {};
            for value in $provided {
                unsafe {
                    // Safety:
                    //
                    // 1. `provider` cannot be shadowed by `$rest` so we are indeed operating on
                    //    the correct type. Additionally, because token trees prevent unbalanced
                    //    groups and the introduction of new async blocks requires a brace, we
                    //    know that we are executing directly in the `async` block provided
                    //    immediately to `SelfRef`.
                    //
                    // 2. We already ensured that the `SelfRefOutput` type was covariant with the
                    //    call to `check_covariance` at the top of the block.
                    //
                    // 3. `$provided` will not expire until the future is finished, which will never
                    //    happen unless we're dropped or the iterator panics (and unwinding respects
                    //    drop order for dependencies due to the lifetimes involved by the return
                    //    values). Because a type either depends on the input lifetime or a static
                    //    lifetime (i.e. it certainly can't shrink as our input lifetime grows), we
                    //    know that the lifetime of our structure is at least the lifetime of the
                    //    value we passed to it.
                    //
                    //    TODO: We need to formalize this statement a bit more.
                    //
                    provider.provide($crate::macro_internals::re_export::Some(value)).await
                };
            }
            unsafe {
                // Safety: see above.
                provider.provide($crate::macro_internals::re_export::None).await
            };
            $crate::macro_internals::re_export::pending::<()>().await;
        })
    };
    (iter for<$lt:lifetime> $ty:ty $(; $future_lt:lifetime)?) => {
        $crate::self_ref![
            iter for<$lt> $ty;
            impl $crate::macro_internals::re_export::Future<Output = ()> $(+ $future_lt)?
        ]
    };
    (iter for<$lt:lifetime> $ty:ty ; $future_ty:ty) => {
        $crate::macro_internals::SelfRef<
            dyn for<$lt> $crate::macro_internals::SelfRefIterOutput<$lt, IterOutput = $ty>,
            $future_ty,
        >
    };

    // === Non-iterator variants === //

    (use $provided:ident in { $($rest:tt)* }) => {
        $crate::macro_internals::SelfRef::new(|provider| async move {
            provider.check_covariance(|_, x| x);
            $($rest)*
            {};
            unsafe {
                // Safety: see above.
                provider.provide($provided).await
            };
            $crate::macro_internals::re_export::pending::<()>().await;
        })
    };
    (for<$lt:lifetime> $ty:ty $(; $future_lt:lifetime)?) => {
        $crate::self_ref![
            for<$lt> $ty;
            impl $crate::macro_internals::re_export::Future<Output = ()> $(+ $future_lt)?
        ]
    };
    (for<$lt:lifetime> $ty:ty ; $future_ty:ty) => {
        $crate::macro_internals::SelfRef<
            dyn for<$lt> $crate::macro_internals::SelfRefOutput<$lt, Output = $ty>,
            $future_ty,
        >
    };
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, iter::Copied, pin::pin, rc::Rc, slice};

    use super::self_ref;

    fn returns_a_slice() -> self_ref![for<'a> (&'a u32, &'a [u32])] {
        self_ref!(use target in {
            let slice = [3, 2, 1, 0];
            let target = slice.split_last().unwrap();
        })
    }

    fn locks_a_guard<T: Copy>(
        a: &Rc<RefCell<Vec<T>>>,
    ) -> self_ref![for<'a> (&'a T, Copied<slice::Iter<'a, T>>); '_] {
        self_ref!(use target in {
            let a = a.borrow();
            let (last, earlier) = a.split_first().unwrap();
            let target = (last, earlier.iter().copied());
        })
    }

    #[test]
    fn simple_usage() {
        let result = pin!(returns_a_slice());
        let (value, my_slice) = result.get();
        assert_eq!(*value, 0);
        assert_eq!(my_slice, &[3, 2, 1]);

        let my_cell = Rc::new(RefCell::new(my_slice.to_vec()));
        {
            let result = pin!(locks_a_guard(&my_cell));
            let (first, mut remaining_iter) = result.get();

            assert_eq!(*first, 3);
            assert_eq!(remaining_iter.next(), Some(2));
            assert_eq!(remaining_iter.next(), Some(1));
            assert_eq!(remaining_iter.next(), None);
        }
        let exclusive = my_cell.borrow_mut();
        assert_eq!(exclusive.as_slice(), &[3, 2, 1]);
    }

    fn never_returns_anything() -> self_ref![for<'a> &'a u32] {
        self_ref!(use t in {
            if true {
                return;
            }

            let t = &3;
        })
    }

    #[test]
    #[should_panic]
    fn early_return() {
        let value = pin!(never_returns_anything());
        value.get();
    }

    fn returns_many_things() -> self_ref![iter for<'a> (i32, &'a mut i32)] {
        self_ref!(use iter t in {
            let mut values = [1, 2, 3];
            let t = values.iter_mut().map(|k| (*k, k));
        })
    }

    #[test]
    fn uses_many_things() {
        for (snapshot, ptr) in pin!(returns_many_things()).iter() {
            println!("{snapshot} {ptr}");
        }
    }
}
