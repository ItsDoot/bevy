use core::{
    any::TypeId,
    cell::Cell,
    pin::Pin,
    task::{Context, Poll},
};
use std::{borrow::Cow, boxed::Box, thread::LocalKey, thread_local, vec::Vec};

use crate::{
    component::Tick,
    schedule::InternedSystemSet,
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
    fn run<'i>(
        self: Box<Self>,
        input: AsyncSystemIn<'i, Self>,
    ) -> Box<dyn AsyncSystemFuture<In = Self::In, Out = Self::Out> + 'i>;

    fn initialize(&mut self, world: &mut World);

    fn check_change_tick(&mut self, change_tick: Tick);

    fn default_system_sets(&self) -> Vec<InternedSystemSet> {
        Vec::new()
    }
}

/// [`AsyncSystem`] types that do not modify the [`World`] when polled. This is implemented for any
/// systems whose parameters all implement [`ReadTickAsyncSystemParam`].
///
/// # Safety
///
/// This must only be implemented for system types which do not mutate the `World` when
/// [`AsyncSystemFuture::poll_unsafe`] is called.
///
/// [`ReadOnlyAsyncSystemParam`]: super::ReadOnlyAsyncSystemParam
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a read-only async system",
    label = "invalid read-only async system"
)]
pub unsafe trait ReadOnlyAsyncSystem: AsyncSystem {
    #[must_use = "async systems do nothing unless you poll them"]
    fn run_readonly<'i>(
        self: Box<Self>,
        input: AsyncSystemIn<'i, Self>,
    ) -> Box<dyn ReadOnlyAsyncSystemFuture<In = Self::In, Out = Self::Out> + 'i>;
}

/// Shorthand way to get the [`AsyncSystem::In`] for an [`AsyncSystem`] as a
/// [`SystemInput::Inner`].
pub type AsyncSystemIn<'i, S> = <<S as AsyncSystem>::In as SystemInput>::Inner<'i>;

pub trait AsyncSystemFuture: Send {
    /// The system's input.
    type In;
    /// The system's output.
    type Out;

    /// Unwraps this system future into its system.
    fn into_system(
        self: Pin<Box<Self>>,
    ) -> Pin<Box<dyn AsyncSystem<In = Self::In, Out = Self::Out>>>;

    /// Polls the system with the given world. Unlike [`AsyncSystemFuture::poll`], this function
    /// can be called in parallel with other systems and may break Rust's aliasing rules if used
    /// incorrectly, making it unsafe to call.
    ///
    /// # Safety
    ///
    /// - The caller must ensure that [`world`](UnsafeWorldCell) has permission to access world
    ///   data registered in `archetype_component_access`. There must be no conflicting
    ///   simultaneous accesses when the system is polled.
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
        // SAFETY:
        // - We have exclusive access to the entire world.
        unsafe { self.poll_unsafe(cx, world_cell) }
    }

    fn check_change_tick(self: Pin<&mut Self>, change_tick: Tick);

    fn get_last_poll(&self) -> Tick;

    fn set_last_poll(self: Pin<&mut Self>, last_poll: Tick);
}

pub trait ReadOnlyAsyncSystemFuture: AsyncSystemFuture {
    /// Unwraps this system future into its system, read-only variant.
    fn into_readonly_system(
        self: Pin<Box<Self>>,
    ) -> Pin<Box<dyn ReadOnlyAsyncSystem<In = Self::In, Out = Self::Out>>>;

    /// Polls the system with the given world.
    ///
    /// Unlike [`AsyncSystemFuture::poll`], this can be called with a shared reference to the
    /// world, since the system is known not to modify the world.
    fn poll_readonly(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        world: &World,
    ) -> Poll<Self::Out> {
        let world_cell = world.as_unsafe_world_cell_readonly();
        // SAFETY:
        // - We have read-only access to the entire world.
        unsafe { self.poll_unsafe(cx, world_cell) }
    }
}

thread_local! {
    /// # Safety
    ///
    /// The lifetime of the stored cell is **NOT** `'static`!
    /// This thread local is akin to a scoped thread local. While there exists libraries like
    /// `scoped-tls` and `scoped-tls-hkt` which could do this for us, they would require closures
    /// in order to access the `World`. However, we want to avoid closures altogether and can do
    /// that safely as long as everytime the system is polled this thread local is filled with a
    /// valid world cell.
    static WORLD: Cell<Option<UnsafeWorldCell<'static>>> = Cell::new(None);
}

pub struct AsyncCtx {
    cell: &'static LocalKey<Cell<Option<UnsafeWorldCell<'static>>>>,
}

impl AsyncCtx {
    pub(crate) fn new(cell: &'static LocalKey<Cell<Option<UnsafeWorldCell<'static>>>>) -> Self {
        Self { cell }
    }

    pub fn as_unsafe_world_cell(&mut self) -> UnsafeWorldCell<'_> {
        self.cell.get().unwrap()
    }

    pub fn as_unsafe_world_cell_readonly(&self) -> UnsafeWorldCell<'_> {
        self.cell.get().unwrap()
    }
}
