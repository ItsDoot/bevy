use alloc::{vec, vec::Vec};

use crate::{
    prelude::{IntoNodeConfigs, IntoSystemSet},
    schedule::{
        traits::{GraphNode, ScheduleGraph},
        InternedSystemSet, NodeConfigs, SystemSet,
    },
};

/// Metadata that specifies the ambiguity resolution strategy for a [`GraphNode`].
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
#[derive(Default)]
pub enum Ambiguities<T> {
    /// Check for any ambiguity warnings.
    #[default]
    Check,
    /// Ignore any ambiguity warnings from the specified targets.
    IgnoreAnyFrom(Vec<T>),
    /// Ignore all ambiguity warnings.
    IgnoreAll,
}

impl<T> Ambiguities<T> {
    /// Marks the [`GraphNode`] as ambiguous with the specified target.
    pub fn ambiguous_with(&mut self, target: T) {
        match self {
            Ambiguities::Check => {
                *self = Ambiguities::IgnoreAnyFrom(vec![target]);
            }
            Ambiguities::IgnoreAnyFrom(targets) => {
                targets.push(target);
            }
            Ambiguities::IgnoreAll => {}
        }
    }

    /// Marks the [`GraphNode`] as ambiguous with all targets.
    pub fn ambiguous_with_all(&mut self) {
        *self = Ambiguities::IgnoreAll;
    }
}

impl<T> AsRef<Self> for Ambiguities<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T> AsMut<Self> for Ambiguities<T> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<N: GraphNode<G>, G: ScheduleGraph> NodeConfigs<N, G> {
    /// Suppess watnings and errors that would result from these nodes having
    /// ambiguities with the specified target.
    pub fn ambiguous_with_inner<T>(&mut self, target: T)
    where
        T: Clone,
        N: GraphNode<G, Metadata: AsMut<Ambiguities<T>>>,
    {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().ambiguous_with(target);
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.ambiguous_with_inner(target.clone());
                }
            }
        }
    }

    /// Suppress warnings and errors that would result from these nodes having
    /// ambiguities with all targets.
    pub fn ambiguous_with_all_inner<T>(&mut self)
    where
        N: GraphNode<G, Metadata: AsMut<Ambiguities<T>>>,
    {
        match self {
            Self::Single(config) => {
                *config.metadata.as_mut() = Ambiguities::IgnoreAll;
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.ambiguous_with_all_inner();
                }
            }
        }
    }
}

/// Types that can be converted into [`NodeConfigs`] with ambiguity resolution.
pub trait IntoAmbiguousNodeConfigs<N, G, Marker>: IntoNodeConfigs<N, G, Marker>
where
    N: GraphNode<G, Metadata: AsMut<Ambiguities<InternedSystemSet>>>,
    G: ScheduleGraph,
{
    /// Suppress warnings and errors that would result from these systems having ambiguities
    /// (conflicting access but indeterminate order) with systems in `set`.
    fn ambiguous_with<M>(self, target: impl IntoSystemSet<M>) -> NodeConfigs<N, G> {
        let mut configs = self.into_configs();
        configs.ambiguous_with_inner(target.into_system_set().intern());
        configs
    }

    /// Suppress warnings and errors that would result from these systems having ambiguities
    /// (conflicting access but indeterminate order) with any other system.
    fn ambiguous_with_all(self) -> NodeConfigs<N, G> {
        let mut configs = self.into_configs();
        configs.ambiguous_with_all_inner();
        configs
    }
}

impl<N, G, Marker, I> IntoAmbiguousNodeConfigs<N, G, Marker> for I
where
    N: GraphNode<G, Metadata: AsMut<Ambiguities<InternedSystemSet>>>,
    G: ScheduleGraph,
    I: IntoNodeConfigs<N, G, Marker>,
{
}
