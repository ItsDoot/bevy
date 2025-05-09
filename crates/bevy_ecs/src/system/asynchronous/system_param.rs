use crate::{system::SystemMeta, world::World};

/// A parameter that can be used in an [`AsyncSystem`](super::AsyncSystem).
pub trait AsyncSystemParam: Sized {
    type State: Send + Sync + 'static;
    type Item<'state>: AsyncSystemParam<State = Self::State>;

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
