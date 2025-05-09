use core::{
    any::TypeId,
    pin::Pin,
    task::{Context, Poll},
};
use std::{borrow::Cow, boxed::Box};

use crate::{
    system::SystemInput,
    world::{unsafe_world_cell::UnsafeWorldCell, World},
};

/// An asynchronous ECS system.
///
/// Async systems are functions with all arguments implementing
/// [`AsyncSystemParam`](super::AsyncSystemParam).
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not an async system",
    label = "invalid async system"
)]
pub trait AsyncSystem: Send + Sync + 'static {
    /// The system's input.
    type In: SystemInput;
    /// The system's output.
    type Out;

    /// Returns the system's name.
    fn name(&self) -> Cow<'static, str>;

    /// Returns the [`TypeId`] of the underlying system type.
    #[inline]
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    #[must_use = "async systems do nothing unless you poll them"]
    fn run<'s>(
        &'s mut self,
        input: AsyncSystemIn<'s, Self>,
    ) -> Box<dyn AsyncSystemFuture<Out = Self::Out> + 's>;

    fn initialize(&mut self, world: &mut World);
}

#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a read-only async system",
    label = "invalid read-only async system"
)]
pub unsafe trait ReadOnlyAsyncSystem: AsyncSystem {
    #[must_use = "async systems do nothing unless you poll them"]
    fn run_readonly<'s>(
        &'s mut self,
        input: AsyncSystemIn<'s, Self>,
    ) -> Box<dyn ReadOnlyAsyncSystemFuture<Out = Self::Out> + 's>;
}

/// Shorthand way to get the [`AsyncSystem::In`] for an [`AsyncSystem`] as a
/// [`SystemInput::Inner`].
pub type AsyncSystemIn<'i, S> = <<S as AsyncSystem>::In as SystemInput>::Inner<'i>;

pub trait AsyncSystemFuture: Send {
    /// The system's output.
    type Out;

    /// Polls the system with the given world. Unlike [`AsyncSystemFuture::poll`], this function
    /// can be called in parallel with other systems and may break Rust's aliasing rules if used
    /// incorrectly, making it unsafe to call.
    ///
    /// # Safety
    ///
    /// - The caller must ensure that [`world`](UnsafeWorldCell) has permission to access world
    ///   data registered in `archetype_component_access`. There must be no conflicting
    ///   simultaneous accesses when the system is polled.
    /// - The method [`AsyncSystemFuture::update_archetype_component_access`] must be called at
    ///   some point before this one, with the same exact [`World`]. If
    ///   [`AsyncSystemFuture::update_archetype_component_access`] panics (or oterhwise does not
    ///   return for any reason), this method must not be called.
    unsafe fn poll_unsafe(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        world: UnsafeWorldCell,
    ) -> Poll<Self::Out>;

    /// Polls the system with the given world.
    ///
    /// For [read-only](ReadOnlyAsyncSystem) systems, see [`ReadOnlyAsyncSystem::run_readonly`] and
    /// [`ReadOnlyAsyncSystemFuture::poll_readonly`], which can be called using `&World`.
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>, world: &mut World) -> Poll<Self::Out> {
        let world_cell = world.as_unsafe_world_cell();
        self.as_mut().update_archetype_component_access(world_cell);
        // SAFETY:
        // - We have exclusive access to the entire world.
        // - `update_archetype_component_access` has been called.
        unsafe { self.poll_unsafe(cx, world_cell) }
    }

    fn update_archetype_component_access(self: Pin<&mut Self>, world: UnsafeWorldCell);
}

pub trait ReadOnlyAsyncSystemFuture: AsyncSystemFuture {
    /// Polls this system with the given world.
    ///
    /// Unlike [`AsyncSystemFuture::poll`], this can be called with a shared reference to the
    /// world, since this system is known not to modify the world.
    fn poll_readonly(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        world: &World,
    ) -> Poll<Self::Out> {
        let world_cell = world.as_unsafe_world_cell_readonly();
        self.as_mut().update_archetype_component_access(world_cell);
        // SAFETY:
        // - We have read-only access to the entire world.
        // - `update_archetype_component_access` has been called.
        unsafe { self.poll_unsafe(cx, world_cell) }
    }
}
