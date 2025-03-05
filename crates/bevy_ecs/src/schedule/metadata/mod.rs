//! Common building blocks for [`GraphNode`] metadata.
//!
//! [`GraphNode`]: crate::schedule::traits::GraphNode

use alloc::boxed::Box;
use core::any::{Any, TypeId};

use bevy_utils::TypeIdMap;

mod ambiguity;
mod chain;
mod condition;
mod dependency;
mod hierarchy;

pub use self::{ambiguity::*, chain::*, condition::*, dependency::*, hierarchy::*};

/// A builder for configuring [`GraphNode`] metadata.
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
#[derive(Default)]
pub struct ConfigOptionBuilder(TypeIdMap<Box<dyn Any>>);

impl ConfigOptionBuilder {
    /// Creates a new builder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts a value into the builder.
    pub fn with<T: 'static>(mut self, value: T) -> Self {
        self.0.insert(TypeId::of::<T>(), Box::new(value));
        self
    }
}
