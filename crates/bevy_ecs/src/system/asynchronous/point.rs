//! Provides [`AsyncSystemAwaitPoint`] labels for when to poll a given [`AsyncSystem`] again.
//!
//! [`AsyncSystem`]: super::AsyncSystem

use bevy_ecs_macros::AsyncSystemAwaitPoint;

use crate::define_label;
pub use crate::schedule::DynEq;

define_label!(
    /// When the [`AsyncSystem`] should be polled again.
    ///
    /// [`AsyncSystem`]: super::AsyncSystem
    AsyncSystemAwaitPoint,
    ASYNC_SYSTEM_AWAIT_POINT_INTERNER
);

/// Informs the async system executor that the async system should be polled as soon as the access
/// is compatible.
#[derive(AsyncSystemAwaitPoint, Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ASAP;

/// Informs the async system executor that the async system should be polled during the next sync
/// point (when commands get applied).
#[derive(AsyncSystemAwaitPoint, Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct NextSync;
