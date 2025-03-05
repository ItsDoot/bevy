use alloc::{boxed::Box, vec::Vec};

use derive_more::derive::{Deref, DerefMut};

use crate::{
    prelude::{Condition, IntoNodeConfigs},
    schedule::{
        traits::{GraphNode, ScheduleGraph},
        BoxedCondition, NodeConfigs,
    },
    system::{IntoSystem, System, SystemInput},
};

/// Conditions that must be met for a [`GraphNode`](crate::schedule::traits::GraphNode) to run.
#[derive(Deref, DerefMut, Default)]
pub struct Conditions<In: SystemInput = ()>(pub Vec<BoxedCondition<In>>);

impl<In: SystemInput> AsRef<Self> for Conditions<In> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<In: SystemInput> AsMut<Self> for Conditions<In> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<N: GraphNode<G>, G: ScheduleGraph> NodeConfigs<N, G> {
    /// Adds a run condition to each individual system in the configuration.
    pub fn distributive_run_if_inner<In, M>(&mut self, condition: impl Condition<M, In> + Clone)
    where
        In: SystemInput,
        N::Metadata: AsMut<Conditions<In>>,
    {
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

    /// Adds a new boxed run condition to the systems.
    ///
    /// This is useful if you have a run condition whose concrete type is unknown.
    /// Prefer `run_if` for run conditions whose type is known at compile time.
    pub fn run_if_dyn<In>(&mut self, condition: BoxedCondition<In>)
    where
        In: SystemInput,
        N::Metadata: AsMut<Conditions<In>>,
        N::GroupMetadata: AsMut<Conditions<In>>,
    {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().push(condition);
            }
            Self::Group { metadata, .. } => {
                metadata.as_mut().push(condition);
            }
        }
    }
}

/// [`GraphNode`]s that can be configured to run conditionally.
pub trait IntoConditionalNodeConfigs<N, G, Marker, In = ()>: IntoNodeConfigs<N, G, Marker>
where
    N: GraphNode<G, Metadata: AsMut<Conditions<In>>, GroupMetadata: AsMut<Conditions<In>>>,
    G: ScheduleGraph,
    In: SystemInput,
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
    fn distributive_run_if<M>(self, condition: impl Condition<M, In> + Clone) -> NodeConfigs<N, G> {
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
    fn run_if<M>(self, condition: impl Condition<M, In>) -> NodeConfigs<N, G> {
        let mut configs = self.into_configs();
        configs.run_if_dyn(new_condition(condition));
        configs
    }
}

impl<N, G, M, In, I> IntoConditionalNodeConfigs<N, G, M, In> for I
where
    N: GraphNode<G, Metadata: AsMut<Conditions<In>>, GroupMetadata: AsMut<Conditions<In>>>,
    G: ScheduleGraph,
    In: SystemInput,
    I: IntoNodeConfigs<N, G, M>,
{
}

fn new_condition<In: SystemInput, M>(condition: impl Condition<M, In>) -> BoxedCondition<In> {
    let condition_system = IntoSystem::into_system(condition);
    assert!(
        condition_system.is_send(),
        "Condition `{}` accesses `NonSend` resources. This is not currently supported.",
        condition_system.name()
    );

    Box::new(condition_system)
}
