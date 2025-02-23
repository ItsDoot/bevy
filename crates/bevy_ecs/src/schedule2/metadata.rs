use alloc::{boxed::Box, vec, vec::Vec};
use core::any::{Any, TypeId};

use bevy_utils::TypeIdMap;
use derive_more::derive::{Deref, DerefMut};

use crate::{
    schedule::{BoxedCondition, Condition, InternedSystemSet, IntoSystemSet, SystemSet},
    schedule2::{
        graph::{Ambiguity, Dependency, DependencyKind},
        GraphNode, IgnoreDeferred, IntoNodeConfigs, NodeConfigs,
    },
    system::{IntoSystem, System},
};

/// Metadata about how the node fits in the schedule graph
#[derive(Default)]
pub struct GraphInfo {
    /// the sets that the node belongs to (hierarchy)
    pub(crate) hierarchy: Vec<InternedSystemSet>,
    /// the sets that the node depends on (must run before or after)
    pub(crate) dependencies: Vec<Dependency>,
    pub(crate) ambiguous_with: Ambiguity,
}

impl GraphInfo {
    fn ambiguous_with(&mut self, set: InternedSystemSet) {
        match &mut self.ambiguous_with {
            detection @ Ambiguity::Check => {
                *detection = Ambiguity::IgnoreWithSet(vec![set]);
            }
            Ambiguity::IgnoreWithSet(ambiguous_with) => {
                ambiguous_with.push(set);
            }
            Ambiguity::IgnoreAll => (),
        }
    }
}

/// A collection of [`Condition`]s that must all be met for a node to run.
#[derive(Deref, DerefMut, Default)]
#[repr(transparent)]
pub struct Conditions(Vec<BoxedCondition>);

impl From<Vec<BoxedCondition>> for Conditions {
    fn from(conditions: Vec<BoxedCondition>) -> Self {
        Self(conditions)
    }
}

impl From<Conditions> for Vec<BoxedCondition> {
    fn from(conditions: Conditions) -> Self {
        conditions.0
    }
}

/// Chain systems into dependencies
#[derive(Default)]
pub enum Chain {
    /// Systems are independent. Nodes are allowed to run in any order.
    #[default]
    Unchained,
    /// Systems are chained. `before -> after` ordering constraints
    /// will be added between the successive elements.
    Chained(TypeIdMap<Box<dyn Any>>),
}

impl Chain {
    /// Returns true if the systems must be chained.
    pub fn is_chained(&self) -> bool {
        matches!(self, Chain::Chained(_))
    }

    /// Specify that the systems must be chained.
    pub fn set_chained(&mut self) {
        if matches!(self, Chain::Unchained) {
            *self = Self::Chained(Default::default());
        };
    }
    /// Specify that the systems must be chained, and add the specified configuration for
    /// all dependencies created between these systems.
    pub fn set_chained_with_config<T: 'static>(&mut self, config: T) {
        self.set_chained();
        if let Chain::Chained(config_map) = self {
            config_map.insert(TypeId::of::<T>(), Box::new(config));
        } else {
            unreachable!()
        };
    }
}

impl<T> NodeConfigs<T>
where
    T: GraphNode<Metadata: AsMut<GraphInfo>>,
{
    /// Adds a new boxed system set to the systems.
    pub fn in_set_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().hierarchy.push(set);
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.in_set_inner(set);
                }
            }
        }
    }

    fn before_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config
                    .metadata
                    .as_mut()
                    .dependencies
                    .push(Dependency::new(DependencyKind::Before, set));
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.before_inner(set);
                }
            }
        }
    }

    fn after_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config
                    .metadata
                    .as_mut()
                    .dependencies
                    .push(Dependency::new(DependencyKind::After, set));
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.after_inner(set);
                }
            }
        }
    }

    fn before_ignore_deferred_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config
                    .metadata
                    .as_mut()
                    .dependencies
                    .push(Dependency::new(DependencyKind::Before, set).add_config(IgnoreDeferred));
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.before_ignore_deferred_inner(set.intern());
                }
            }
        }
    }

    fn after_ignore_deferred_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config
                    .metadata
                    .as_mut()
                    .dependencies
                    .push(Dependency::new(DependencyKind::After, set).add_config(IgnoreDeferred));
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.after_ignore_deferred_inner(set.intern());
                }
            }
        }
    }

    fn ambiguous_with_inner(&mut self, set: InternedSystemSet) {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().ambiguous_with(set);
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.ambiguous_with_inner(set);
                }
            }
        }
    }

    fn ambiguous_with_all_inner(&mut self) {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().ambiguous_with = Ambiguity::IgnoreAll;
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.ambiguous_with_all_inner();
                }
            }
        }
    }
}

impl<T> NodeConfigs<T>
where
    T: GraphNode<Metadata: AsMut<Conditions>, GroupMetadata: AsMut<Conditions>>,
{
    /// Adds a new boxed run condition to the systems.
    ///
    /// This is useful if you have a run condition whose concrete type is unknown.
    /// Prefer `run_if` for run conditions whose type is known at compile time.
    pub fn run_if_dyn(&mut self, condition: BoxedCondition) {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().push(condition);
            }
            Self::Group { metadata, .. } => {
                metadata.as_mut().push(condition);
            }
        }
    }

    fn distributive_run_if_inner<M>(&mut self, condition: impl Condition<M> + Clone) {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().push(new_condition(condition));
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.distributive_run_if_inner(condition.clone());
                }
            }
        }
    }
}

impl<T> NodeConfigs<T>
where
    T: GraphNode<GroupMetadata: AsMut<Chain>>,
{
    fn chain_inner(&mut self) {
        match self {
            Self::Single(_) => { /* no op */ }
            Self::Group { metadata, .. } => {
                metadata.as_mut().set_chained();
            }
        }
    }

    fn chain_ignore_deferred_inner(&mut self) {
        match self {
            Self::Single(_) => { /* no op */ }
            Self::Group { metadata, .. } => {
                metadata.as_mut().set_chained_with_config(IgnoreDeferred);
            }
        }
    }
}

/// Configuration options for ordering systems.
pub trait IntoOrderedNodeConfigs<N, Marker>: IntoNodeConfigs<N, Marker>
where
    N: GraphNode<Metadata: AsMut<GraphInfo>>,
{
    /// Add these systems to the provided `set`.
    fn in_set(self, set: impl SystemSet) -> NodeConfigs<N> {
        assert!(
            set.system_type().is_none(),
            "adding arbitrary systems to a system type set is not allowed"
        );

        let mut configs = self.into_configs();
        configs.in_set_inner(set.intern());
        configs
    }

    /// Runs before all systems in `set`. If `self` has any systems that produce [`Commands`](crate::system::Commands)
    /// or other [`Deferred`](crate::system::Deferred) operations, all systems in `set` will see their effect.
    ///
    /// If automatically inserting [`ApplyDeferred`](crate::schedule::ApplyDeferred) like
    /// this isn't desired, use [`before_ignore_deferred`](Self::before_ignore_deferred) instead.
    ///
    /// Calling [`.chain`](Self::chain) is often more convenient and ensures that all systems are added to the schedule.
    /// Please check the [caveats section of `.after`](Self::after) for details.
    fn before<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.before_inner(set.intern());
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
    fn after<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.after_inner(set.intern());
        configs
    }

    /// Run before all systems in `set`.
    ///
    /// Unlike [`before`](Self::before), this will not cause the systems in
    /// `set` to wait for the deferred effects of `self` to be applied.
    fn before_ignore_deferred<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.before_ignore_deferred_inner(set.intern());
        configs
    }

    /// Run after all systems in `set`.
    ///
    /// Unlike [`after`](Self::after), this will not wait for the deferred
    /// effects of systems in `set` to be applied.
    fn after_ignore_deferred<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.after_ignore_deferred_inner(set.intern());
        configs
    }

    /// Suppress warnings and errors that would result from these systems having ambiguities
    /// (conflicting access but indeterminate order) with systems in `set`.
    fn ambiguous_with<M>(self, set: impl IntoSystemSet<M>) -> NodeConfigs<N> {
        let set = set.into_system_set();
        let mut configs = self.into_configs();
        configs.ambiguous_with_inner(set.intern());
        configs
    }

    /// Suppress warnings and errors that would result from these systems having ambiguities
    /// (conflicting access but indeterminate order) with any other system.
    fn ambiguous_with_all(self) -> NodeConfigs<N> {
        let mut configs = self.into_configs();
        configs.ambiguous_with_all_inner();
        configs
    }
}

impl<N, Marker, I> IntoOrderedNodeConfigs<N, Marker> for I
where
    N: GraphNode<Metadata: AsMut<GraphInfo>>,
    I: IntoNodeConfigs<N, Marker>,
{
}

/// Configuration options for adding conditions to systems.
pub trait IntoConditionalNodeConfigs<N, Marker>: IntoNodeConfigs<N, Marker>
where
    N: GraphNode<Metadata: AsMut<Conditions>, GroupMetadata: AsMut<Conditions>>,
{
    /// Add a run condition to each contained system.
    ///
    /// Each system will receive its own clone of the [`Condition`] and will only run
    /// if the `Condition` is true.
    ///
    /// Each individual condition will be evaluated at most once (per schedule run),
    /// right before the corresponding system prepares to run.
    ///
    /// This is equivalent to calling [`run_if`](IntoSystemConfigs::run_if) on each individual
    /// system, as shown below:
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// # let mut schedule = Schedule::default();
    /// # fn a() {}
    /// # fn b() {}
    /// # fn condition() -> bool { true }
    /// schedule.add_systems((a, b).distributive_run_if(condition));
    /// schedule.add_systems((a.run_if(condition), b.run_if(condition)));
    /// ```
    ///
    /// # Note
    ///
    /// Because the conditions are evaluated separately for each system, there is no guarantee
    /// that all evaluations in a single schedule run will yield the same result. If another
    /// system is run inbetween two evaluations it could cause the result of the condition to change.
    ///
    /// Use [`run_if`](IntoSystemSetConfigs::run_if) on a [`SystemSet`] if you want to make sure
    /// that either all or none of the systems are run, or you don't want to evaluate the run
    /// condition for each contained system separately.
    fn distributive_run_if<M>(self, condition: impl Condition<M> + Clone) -> NodeConfigs<N> {
        let mut configs = self.into_configs();
        configs.distributive_run_if_inner(condition);
        configs
    }

    /// Run the systems only if the [`Condition`] is `true`.
    ///
    /// The `Condition` will be evaluated at most once (per schedule run),
    /// the first time a system in this set prepares to run.
    ///
    /// If this set contains more than one system, calling `run_if` is equivalent to adding each
    /// system to a common set and configuring the run condition on that set, as shown below:
    ///
    /// # Examples
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// # let mut schedule = Schedule::default();
    /// # fn a() {}
    /// # fn b() {}
    /// # fn condition() -> bool { true }
    /// # #[derive(SystemSet, Debug, Eq, PartialEq, Hash, Clone, Copy)]
    /// # struct C;
    /// schedule.add_systems((a, b).run_if(condition));
    /// schedule.add_systems((a, b).in_set(C)).configure_sets(C.run_if(condition));
    /// ```
    ///
    /// # Note
    ///
    /// Because the condition will only be evaluated once, there is no guarantee that the condition
    /// is upheld after the first system has run. You need to make sure that no other systems that
    /// could invalidate the condition are scheduled inbetween the first and last run system.
    ///
    /// Use [`distributive_run_if`](IntoSystemConfigs::distributive_run_if) if you want the
    /// condition to be evaluated for each individual system, right before one is run.
    fn run_if<M>(self, condition: impl Condition<M>) -> NodeConfigs<N> {
        let mut configs = self.into_configs();
        configs.run_if_dyn(new_condition(condition));
        configs
    }
}

impl<N, Marker, I> IntoConditionalNodeConfigs<N, Marker> for I
where
    N: GraphNode<Metadata: AsMut<Conditions>, GroupMetadata: AsMut<Conditions>>,
    I: IntoNodeConfigs<N, Marker>,
{
}

/// Configuration options for chaining systems together.
pub trait IntoChainableNodeConfigs<N, Marker>: IntoNodeConfigs<N, Marker>
where
    N: GraphNode<GroupMetadata: AsMut<Chain>>,
{
    /// Treat this collection as a sequence of systems.
    ///
    /// Ordering constraints will be applied between the successive elements.
    ///
    /// If the preceding node on an edge has deferred parameters, an [`ApplyDeferred`](crate::schedule::ApplyDeferred)
    /// will be inserted on the edge. If this behavior is not desired consider using
    /// [`chain_ignore_deferred`](Self::chain_ignore_deferred) instead.
    fn chain(self) -> NodeConfigs<N> {
        let mut configs = self.into_configs();
        configs.chain_inner();
        configs
    }

    /// Treat this collection as a sequence of systems.
    ///
    /// Ordering constraints will be applied between the successive elements.
    ///
    /// Unlike [`chain`](Self::chain) this will **not** add [`ApplyDeferred`](crate::schedule::ApplyDeferred) on the edges.
    fn chain_ignore_deferred(self) -> NodeConfigs<N> {
        let mut configs = self.into_configs();
        configs.chain_ignore_deferred_inner();
        configs
    }
}

impl<N, Marker, I> IntoChainableNodeConfigs<N, Marker> for I
where
    N: GraphNode<GroupMetadata: AsMut<Chain>>,
    I: IntoNodeConfigs<N, Marker>,
{
}

fn new_condition<M>(condition: impl Condition<M>) -> BoxedCondition {
    let condition_system = IntoSystem::into_system(condition);
    assert!(
        condition_system.is_send(),
        "Condition `{}` accesses `NonSend` resources. This is not currently supported.",
        condition_system.name()
    );

    Box::new(condition_system)
}
