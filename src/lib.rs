#![no_std]

#[doc(hidden)]
pub mod macro_internals {
    use core::{
        cell::Cell,
        future::Future,
        marker::PhantomData,
        mem::{transmute, ManuallyDrop},
        pin::Pin,
        ptr,
        task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
    };

    pub mod re_export {
        pub use core::{
            future::Future,
            option::Option::{None, Some},
        };
    }

    mod sealed {
        pub trait CannotBeImplemented {}
    }

    fn dummy_waker() -> ManuallyDrop<Waker> {
        const VTABLE: RawWakerVTable = RawWakerVTable::new(
            |data| RawWaker::new(data, &VTABLE),
            |_data| {},
            |_data| {},
            |_data| {},
        );

        ManuallyDrop::new(unsafe { Waker::from_raw(RawWaker::new(ptr::null(), &VTABLE)) })
    }

    type Feed<'a, T_> = <T_ as SelfRefOutput<'a>>::Output;

    pub trait SelfRefOutput<'a>: sealed::CannotBeImplemented {
        type Output;
    }

    pub struct SelfRef<T: ?Sized, F> {
        _ty: PhantomData<fn(T) -> T>,
        future: F,
    }

    impl<T, F> SelfRef<T, F>
    where
        T: ?Sized + for<'a> SelfRefOutput<'a>,
        F: Future<Output = ()>,
    {
        #[inline(always)]
        pub fn new<G>(generator: G) -> Self
        where
            G: FnOnce(SelfRefProvider<T>) -> F,
        {
            Self {
                _ty: PhantomData,
                future: generator(SelfRefProvider { _ty: PhantomData }),
            }
        }

        #[inline(always)]
        pub fn get<'a>(self: Pin<&'a mut Self>) -> Feed<'a, T> {
            let future = unsafe {
                // Safety: `future` is structurally pinned, we decided.
                self.map_unchecked_mut(|me| &mut me.future)
            };

            // Create a context with a dummy waker.
            // N.B. We wrap our waker in a `SelfRefProviderFuture` to ensure that early returns don't
            // cause issues.
            let dummy_waker = SelfRefProviderFuture::<Feed<'a, T>>(dummy_waker(), Cell::new(None));

            let mut context = Context::from_waker(&dummy_waker.0);

            // Poll the future to force `SelfRefProviderFuture` to replace the waker.
            let _ = future.poll(&mut context);

            // Fetch the new waker, which is the first field in a `SelfRefProviderFuture`.
            let SelfRefProviderFuture(_, data) = unsafe {
                // Safety: Because `Context<'_>` is invariant w.r.t `'_` and the `'_` lifetime is
                // existential for invocations of `Future:poll`, we know that our `Context`'s waker
                // could not have been mutated safely unless it had been mutated by a
                // `SelfRefProviderFuture` with the appropriate type parameter. We know that, if the
                // replacement went through, we'll be reading from `SelfRefProviderFuture<Feed<'b, T>>`
                // for some `'b`.
                //
                // By the safety guarantees of `SelfRefProvider::provide`, we know that our type `T`
                // is covariant w.r.t `'b`. Additional, because the invocation of the
                // `SelfRefProvider::provide` future will last for the entire remaining lifetime of
                // the closure future, the value passed to the future (living for `'a`) will live at
                // least as long as `&'a mut Self`. In other words, `'b: 'a`. Hence, although the
                // lifetimes of our invocation and the `async` closure's invocation may not be
                // identical, they are still assignable to one another.
                //
                // Hence, it is valid to reinterpret our `&Waker` as a `&SelfRefProviderFuture`.
                &*(context.waker() as *const Waker).cast::<SelfRefProviderFuture<Feed<'a, T>>>()
            };

            // Fetch the data from the future.
            data.replace(None)
                .expect("Cannot call `SelfRef::get` more than once.")
        }
    }

    pub struct SelfRefProvider<T: ?Sized> {
        _ty: PhantomData<fn(T) -> T>,
    }

    impl<T: ?Sized + for<'a> SelfRefOutput<'a>> SelfRefProvider<T> {
        // Safety:
        //
        // - This may only be `.await`'ed by `async` contexts evaluated by `SelfRef::<T>::get()`
        //   where `T` has the same type as the `T` in `SelfRefProvider<T>`.
        //
        // - `T` must be covariant w.r.t `'a` (this can be verified in macros using `check_covariance`)
        //
        // - The returned future must be alive for as long as the future generated for `SelfRef::new`.
        //   In other words, this future must be blocking.
        //
        #[inline(always)]
        pub async unsafe fn provide(self, output: Feed<'_, T>) {
            SelfRefProviderFuture(dummy_waker(), Cell::new(Some(output))).await;
        }

        // Many thanks to Yandros for the macro help!
        //  Github: https://github.com/danielhenrymantilla
        pub fn check_covariance(
            &self,
            _: impl for<'l, 's> FnOnce(
                [&'s &'l (); 0],
                *const *const Feed<'l, T>,
            ) -> *const *const Feed<'s, T>,
        ) {
        }
    }

    #[repr(C)]
    struct SelfRefProviderFuture<T>(ManuallyDrop<Waker>, Cell<Option<T>>);

    impl<T> Unpin for SelfRefProviderFuture<T> {}

    impl<T> Future for SelfRefProviderFuture<T> {
        type Output = ();

        #[inline(always)]
        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            let me = self.get_mut();

            *cx = unsafe {
                // Safety: by the safety guarantees of `SelfRefOutput::provide`, we are guaranteed
                //  to be called exclusively in response to a poll by `SelfRef::get`, which expects
                //  a context living for at least the `get` call. Being a part of the `future` being
                //  called, we know that we live for the lifetime of the `SelfRef` itself so we have
                //  no issues satisfying this lifetime constraint.
                //
                //  Technically, `Context<'a>` is invariant w.r.t `'a` so outliving is not strictly
                //  allowed but this feature isn't used for the standard `from_waker` constructor and
                //  I don't think they can add metadata in the future that is actually contravariant
                //  without creating new methods for it.
                //
                //  The important part, here, is that we replace the reference to the waker with a
                //  reference to a waker embedded in a `SelfRefProviderFuture` so that the caller can
                //  get access to the `Cell<Option<T>>`.
                //
                //  In the future, when `waker_getters` stabilizes (#96992), we should be able to
                //  communicate entirely through the `RawWaker`'s `data` field, which should make
                //  this less magical.
                transmute(Context::from_waker(&me.0))
            };
            Poll::Pending
        }
    }
}

#[macro_export]
macro_rules! self_ref {
    (use $provided:ident in { $($rest:tt)* }) => {
        $crate::macro_internals::SelfRef::new(|__self_ref_internal_and_very_unsafe_provider| async move {
            __self_ref_internal_and_very_unsafe_provider.check_covariance(|_, x| x);

            $($rest)*

            // This block protects us from trailing closures.
            {};

            unsafe {
                // Safety:
                //
                // - We are guaranteed to be executing in an appropriate context because this `async`
                //   block is given directly to `SelfRef` and all token trees are balanced so `$rest`
                //   could not have moved us into a different async block. We know that this is the
                //   appropriate `__self_ref_internal_and_very_unsafe_provider` with the appropriate
                //   type for the closure because no one else could have bound to this variable
                //   without being particularly malicious, at which point we can't help them.
                //
                // - We've already proven that `T` is covariant through `check_covariance`.
                //
                // - Because we're executing in the main `async` block and `provide` is inherently
                //   blocking, we know that the entire future will be blocked as long as we provide
                //   `$provided` to the caller.
                //
                __self_ref_internal_and_very_unsafe_provider.provide($provided).await;
            }
        })
    };
    (for<$lt:lifetime> $ty:ty $(; $future_lt:lifetime)?) => {
        $crate::macro_internals::SelfRef<
            dyn for<$lt> $crate::macro_internals::SelfRefOutput<$lt, Output = $ty>,
            impl $crate::macro_internals::re_export::Future<Output = ()> $(+ $future_lt)?,
        >
    };
}
