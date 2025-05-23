use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use variadics_please::all_tuples;

use crate::{
    system::{AsyncCtx, SystemMeta, SystemParam},
    world::World,
};

/// A parameter that can be used in an [`AsyncSystem`](super::AsyncSystem).
pub trait AsyncSystemParam: Sized {
    /// Used to store data which persists across invocations of an async system.
    type State: Send + Sync + 'static;

    /// The item type returned when constructing this async system param.
    /// This value of this associated type should be `Self`, instantiated with new lifetimes.
    ///
    /// You could think of [`AsyncSystemParam::Item<'w, 's>`] as being an *operation* that changes
    /// the lifetimes bound to `Self`.
    type Item<'state>: AsyncSystemParam<State = Self::State> + Send;

    fn init_state(world: &mut World, system_meta: &mut SystemMeta) -> Self::State;
}

/// An [`AsyncSystemParam`] that never causes a mutation of the [`World`] post-initialization.
///
/// # Safety
///
/// This must only be implemented for [`AsyncSystemParam`] impls that exclusively read the [`World`].
pub unsafe trait ReadOnlyAsyncSystemParam: AsyncSystemParam {}

/// Shorthand way of accessing the associated type [`AsyncSystemParam::Item`] for a given [`AsyncSystemParam`].
pub type AsyncSystemParamItem<'state, P> = <P as AsyncSystemParam>::Item<'state>;

pub struct Async<'state, P: SystemParam> {
    _marker: PhantomData<&'state P>,
}

impl<'s, P: SystemParam> Async<'s, P> {
    pub async fn asap<'w>(&mut self, world: &'w mut AsyncCtx) -> AsyncItem<'w, 's, P> {
        todo!()
    }

    pub async fn next_sync<'w>(&mut self, world: &'w mut AsyncCtx) -> AsyncItem<'w, 's, P> {
        todo!()
    }
}

pub struct AsyncItem<'world, 'state, P: SystemParam> {
    item: P::Item<'world, 'state>,
}

impl<'w, 's, P: SystemParam> Deref for AsyncItem<'w, 's, P> {
    type Target = P::Item<'w, 's>;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<'w, 's, P: SystemParam> DerefMut for AsyncItem<'w, 's, P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}

macro_rules! impl_async_system_param_tuple {
    ($(#[$meta:meta])* $($param: ident),*) => {
        #[expect(
            clippy::allow_attributes,
            reason = "This is in a macro, and as such, the below lints may not always apply."
        )]
        #[allow(
            non_snake_case,
            reason = "Certain variable names are provided by the caller, not by us."
        )]
        #[allow(
            unused_variables,
            reason = "Zero-length tuples won't use some of the parameters."
        )]
        $(#[$meta])*
        impl <$($param: AsyncSystemParam),*> AsyncSystemParam for ($($param,)*) {
            type State = ($($param::State,)*);
            type Item<'state> = ($($param::Item::<'state>,)*);

            #[inline]
            fn init_state(world: &mut World, system_meta: &mut SystemMeta) -> Self::State {
                (($($param::init_state(world, system_meta),)*))
            }
        }

        $(#[$meta])*
        // SAFETY: tuple consists only of ReadOnlyAsyncSystemParams
        unsafe impl<$($param: ReadOnlyAsyncSystemParam),*> ReadOnlyAsyncSystemParam for ($($param,)*) {}
    };
}

all_tuples!(
    #[doc(fake_variadic)]
    impl_async_system_param_tuple,
    0,
    16,
    P
);
