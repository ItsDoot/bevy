use alloc::{boxed::Box, vec::Vec};
use core::any::{Any, TypeId};
use derive_more::derive::{Deref, DerefMut};

use bevy_utils::TypeIdMap;

use crate::{
    prelude::{IntoNodeConfigs, IntoSystemSet},
    schedule::{
        passes::IgnoreDeferred,
        traits::{GraphNode, ScheduleGraph},
        ConfigOptionBuilder, InternedSystemSet, NodeConfigs, SystemSet,
    },
};

/// Metadata that specifies ordering dependencies of a [`GraphNode`].
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
#[derive(Deref, DerefMut)]
pub struct Dependencies<T>(pub Vec<Dependency<T>>);

impl<T> Default for Dependencies<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> AsRef<Self> for Dependencies<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T> AsMut<Self> for Dependencies<T> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

/// A dependency between two [`GraphNode`]s. The dependency specifies the kind of
/// dependency and the target node to subject the dependency to.
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
pub struct Dependency<T> {
    /// The dependency direction.
    pub kind: DependencyKind,
    /// The node to order against.
    pub target: T,
    /// Additional options for the dependency.
    pub options: TypeIdMap<Box<dyn Any>>,
}

impl<T> Dependency<T> {
    /// Creates a new dependency with the specified kind targeting the specified
    /// node.
    pub fn new(kind: DependencyKind, target: T) -> Self {
        Self {
            kind,
            target,
            options: TypeIdMap::default(),
        }
    }

    /// Adds an option to the dependency.
    pub fn with_option<O: 'static>(mut self, config: O) -> Self {
        self.options.insert(TypeId::of::<O>(), Box::new(config));
        self
    }

    /// Sets the options for the dependency.
    pub fn with_options(mut self, options: ConfigOptionBuilder) -> Self {
        self.options = options.0;
        self
    }
}

/// The kind of dependency between two [`GraphNode`]s.
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum DependencyKind {
    /// The node should be visited before the target node.
    Before,
    /// The node should be visited after the target node.
    After,
}

impl<N: GraphNode<G>, G: ScheduleGraph> NodeConfigs<N, G> {
    /// Adds a dependency to the systems in the configuration.
    pub fn add_dependency_inner<T: Clone>(
        &mut self,
        kind: DependencyKind,
        target: T,
        mut options: impl FnMut() -> ConfigOptionBuilder,
    ) where
        N::Metadata: AsMut<Dependencies<T>>,
    {
        match self {
            NodeConfigs::Single(config) => {
                config
                    .metadata
                    .as_mut()
                    .push(Dependency::new(kind, target).with_options(options()));
            }
            NodeConfigs::Group { configs, .. } => {
                for config in configs {
                    config.add_dependency_inner(kind, target.clone(), &mut options);
                }
            }
        }
    }
}

/// [`GraphNode`]s that can be configured to run in a specific order.
pub trait IntoOrderedNodeConfigs<N, G, Marker>: IntoNodeConfigs<N, G, Marker>
where
    N: GraphNode<G, Metadata: AsMut<Dependencies<InternedSystemSet>>>,
    G: ScheduleGraph,
{
    /// Runs before all systems in `set`. If `self` has any systems that produce [`Commands`](crate::system::Commands)
    /// or other [`Deferred`](crate::system::Deferred) operations, all systems in `set` will see their effect.
    ///
    /// If automatically inserting [`ApplyDeferred`](crate::schedule::ApplyDeferred) like
    /// this isn't desired, use [`before_ignore_deferred`](Self::before_ignore_deferred) instead.
    ///
    /// Calling [`.chain`](Self::chain) is often more convenient and ensures that all systems are added to the schedule.
    /// Please check the [caveats section of `.after`](Self::after) for details.
    fn before<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N, G> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.add_dependency_inner(DependencyKind::Before, set.intern(), || {
            ConfigOptionBuilder::default()
        });
        configs
    }

    /// Run after all systems in `set`. If `set` has any systems that produce [`Commands`](crate::system::Commands)
    /// or other [`Deferred`](crate::system::Deferred) operations, all systems in `self` will see their effect.
    ///
    /// If automatically inserting [`ApplyDeferred`](crate::schedule::ApplyDeferred) like
    /// this isn't desired, use [`after_ignore_deferred`](Self::after_ignore_deferred) instead.
    ///
    /// Calling [`.chain`](Self::chain) is often more convenient and ensures that all systems are added to the schedule.
    ///
    /// # Caveats
    ///
    /// If you configure two [`System`]s like `(GameSystem::A).after(GameSystem::B)` or `(GameSystem::A).before(GameSystem::B)`, the `GameSystem::B` will not be automatically scheduled.
    ///
    /// This means that the system `GameSystem::A` and the system or systems in `GameSystem::B` will run independently of each other if `GameSystem::B` was never explicitly scheduled with [`configure_sets`]
    /// If that is the case, `.after`/`.before` will not provide the desired behavior
    /// and the systems can run in parallel or in any order determined by the scheduler.
    /// Only use `after(GameSystem::B)` and `before(GameSystem::B)` when you know that `B` has already been scheduled for you,
    /// e.g. when it was provided by Bevy or a third-party dependency,
    /// or you manually scheduled it somewhere else in your app.
    ///
    /// Another caveat is that if `GameSystem::B` is placed in a different schedule than `GameSystem::A`,
    /// any ordering calls between them—whether using `.before`, `.after`, or `.chain`—will be silently ignored.
    ///
    /// [`configure_sets`]: https://docs.rs/bevy/latest/bevy/app/struct.App.html#method.configure_sets
    fn after<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N, G> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.add_dependency_inner(DependencyKind::After, set.intern(), || {
            ConfigOptionBuilder::default()
        });
        configs
    }

    /// Run before all systems in `set`.
    ///
    /// Unlike [`before`](Self::before), this will not cause the systems in
    /// `set` to wait for the deferred effects of `self` to be applied.
    fn before_ignore_deferred<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N, G> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.add_dependency_inner(DependencyKind::Before, set.intern(), || {
            ConfigOptionBuilder::default().with(IgnoreDeferred)
        });
        configs
    }

    /// Run after all systems in `set`.
    ///
    /// Unlike [`after`](Self::after), this will not wait for the deferred
    /// effects of systems in `set` to be applied.
    fn after_ignore_deferred<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N, G> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.add_dependency_inner(DependencyKind::After, set.intern(), || {
            ConfigOptionBuilder::default().with(IgnoreDeferred)
        });
        configs
    }
}

impl<N, G, M, I> IntoOrderedNodeConfigs<N, G, M> for I
where
    N: GraphNode<G, Metadata: AsMut<Dependencies<InternedSystemSet>>>,
    G: ScheduleGraph,
    I: IntoNodeConfigs<N, G, M>,
{
}
