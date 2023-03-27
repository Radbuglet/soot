#![cfg_attr(not(test), no_std)]

#[doc(hidden)]
pub mod macro_internals {
    use core::{
        cell::UnsafeCell,
        future::Future,
        iter,
        marker::PhantomData,
        mem::{transmute, ManuallyDrop, MaybeUninit},
        pin::Pin,
        ptr,
        task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
    };

    pub mod re_export {
        pub use core::{
            future::{pending, Future},
            option::Option::{None, Some},
        };
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

    type Feed<'a, T> = <T as SelfRefOutput<'a>>::Output;
    type FeedIter<'a, T> = <T as SelfRefIterOutput<'a>>::IterOutput;

    pub trait SelfRefOutput<'a> {
        type Output;
    }

    pub trait SelfRefIterOutput<'a> {
        type IterOutput;
    }

    impl<'a, T: ?Sized + SelfRefIterOutput<'a>> SelfRefOutput<'a> for T {
        type Output = Option<T::IterOutput>;
    }

    pub struct SelfRef<T: ?Sized, F> {
        _ty: PhantomData<fn(T) -> T>,
        future: UnsafeCell<F>,
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
                future: UnsafeCell::new(generator(SelfRefProvider { _ty: PhantomData })),
            }
        }

        #[inline(always)]
        pub fn get_streaming<'a>(self: Pin<&'a Self>) -> Feed<'a, T> {
            let future = unsafe { Pin::new_unchecked(&mut *self.future.get()) };

            let dummy_waker = SelfRefProviderFuture::<Feed<'a, T>> {
                waker: dummy_waker(),
                output: None,
                should_wake: false,
            };

            let mut context = Context::from_waker(&dummy_waker.waker);

            let _ = future.poll(&mut context);

            let SelfRefProviderFuture { output, .. } = unsafe {
                &*(context.waker() as *const Waker as *const SelfRefProviderFuture<Feed<'a, T>>)
            };

            unsafe {
                output
                    .as_ref()
                    .expect(
                        "`SelfRef` provider never provided a value. Was there an unexpected early \
                         return or an excess of reads?",
                    )
                    .assume_init_read()
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
        pub fn iter_streaming<'a>(
            self: Pin<&'a Self>,
        ) -> impl Iterator<Item = FeedIter<'a, T>> + 'a {
            iter::from_fn(move || self.get_streaming())
        }

        pub fn iter<'a>(self: Pin<&'a mut Self>) -> impl Iterator<Item = FeedIter<'a, T>> + 'a {
            self.into_ref().iter_streaming()
        }
    }

    pub struct SelfRefProvider<T: ?Sized> {
        _ty: PhantomData<fn(T) -> T>,
    }

    impl<T: ?Sized + for<'a> SelfRefOutput<'a>> SelfRefProvider<T> {
        #[inline(always)]
        pub async unsafe fn provide(&self, output: Feed<'_, T>) {
            SelfRefProviderFuture {
                waker: dummy_waker(),
                output: Some(MaybeUninit::new(output)),
                should_wake: false,
            }
            .await;
        }

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
                *cx = unsafe { transmute(Context::from_waker(&me.waker)) };
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
                unsafe { provider.provide($crate::macro_internals::re_export::Some(value)).await };
            }
            unsafe { provider.provide($crate::macro_internals::re_export::None).await };
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
            unsafe { provider.provide($provided).await };
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
