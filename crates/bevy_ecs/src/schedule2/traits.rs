use alloc::{boxed::Box, vec::Vec};
use core::{error::Error, fmt::Debug, hash::Hash};

use crate::{
    component::Tick,
    schedule2::{
        InternedScheduleLabel, NodeConfig, NodeConfigs, ScheduleBuildPass, ScheduleExecutor,
    },
    world::World,
};

/// Stores nodes for a [`Schedule`] and how they are connected.
///
/// This type is meant to be optimized for introspection and mutation, not
/// execution. For an execution-optimized version, see [`ScheduleExecutable`].
///
/// [`Schedule`]: super::Schedule
pub trait ScheduleGraph: Default + Send + Sync + 'static {
    /// The type of unique identifier for a node in the graph.
    type Id: GraphNodeId;
    /// The type of executable container for the graph. Usually implies
    /// topological sorting.
    type Executable: ScheduleExecutable;
    /// Error type that can occur when building the executable.
    type BuildError: Error;
    /// The type of settings available for the graph when building.
    type BuildSettings: Clone;
    /// The kind of executors supported by the graph.
    type ExecutorKind: Clone + Copy + PartialEq + Eq + Debug + Default;
    /// Metadata stored for all schedules of this type.
    type GlobalMetadata: Clone + Default + Send + Sync + 'static;

    /// Creates a new executor for the graph with the given label.
    fn new_executor(kind: Self::ExecutorKind) -> Box<dyn ScheduleExecutor<Self>>;

    /// Returns true if the graph has changed since the last build.
    fn changed(&self) -> bool;

    /// Sets the changed state of the graph.
    fn set_changed(&mut self, changed: bool);

    /// Adds a custom build pass to the graph.
    fn add_build_pass<P: ScheduleBuildPass<Self>>(&mut self, pass: P);

    /// Removes a custom build pass from the graph.
    fn remove_build_pass<P: ScheduleBuildPass<Self>>(&mut self);

    /// Returns the graph's current build settings.
    fn get_build_settings(&self) -> &Self::BuildSettings;

    /// Sets the graph's build settings.
    fn set_build_settings(&mut self, settings: Self::BuildSettings);

    /// Initializes all nodes in the graph for the given world.
    fn initialize(&mut self, world: &mut World);

    /// Updates the [`ScheduleExecutable`] based on the current state of the graph.
    // TODO: add ignored_ambiguities argument
    fn update(
        &mut self,
        world: &mut World,
        executable: &mut Self::Executable,
        global_metadata: &Self::GlobalMetadata,
        label: InternedScheduleLabel,
    ) -> Result<(), Self::BuildError>;
}

/// Shorthand for the node ID type of a [`ScheduleGraph`].
pub type SGNodeId<G> = <G as ScheduleGraph>::Id;

/// Shorthand for the build error type of a [`ScheduleGraph`].
pub type SGBuildError<G> = <G as ScheduleGraph>::BuildError;

/// Stores nodes for a [`Schedule`] in a form optimized for execution by
/// [`ScheduleExecutor`]s.
///
/// [`Schedule`]: super::Schedule
/// [`ScheduleExecutor`]: super::ScheduleExecutor
pub trait ScheduleExecutable: Default + Send + Sync + 'static {
    /// Applies commands from executed nodes to the given world.
    fn apply_deferred(&mut self, world: &mut World);

    /// Iterates the change ticks of all nodes in the schedule and clamps any
    /// older than [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    fn check_change_ticks(&mut self, change_tick: Tick);
}

/// Trait for nodes to define how they get added to a [`ScheduleGraph`].
pub trait GraphNode: Sized {
    /// Metadata used to configure the node.
    type Metadata;
    /// Metadata used to configure a group of nodes.
    type GroupMetadata: Default;
    /// Extra data returned when processing a group of nodes.
    type ProcessData;
    /// The graph type this node is for.
    type Graph: ScheduleGraph;

    /// Converts this node into a configuration.
    fn into_config(self) -> NodeConfig<Self>;

    /// Processes a single node of this type and adds it to the graph.
    fn process_config(
        graph: &mut Self::Graph,
        config: NodeConfig<Self>,
    ) -> Result<SGNodeId<Self::Graph>, SGBuildError<Self::Graph>>;

    /// Processes one or more nodes of this type and adds them to the graph.
    fn process_configs(
        graph: &mut Self::Graph,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self>, SGBuildError<Self::Graph>>;
}

/// Result of calling [`GraphNode::process_configs`].
pub struct ProcessedConfigs<G: GraphNode> {
    /// The nodes that were processed.
    pub nodes: Vec<<G::Graph as ScheduleGraph>::Id>,
    /// Extra data returned from processing the nodes.
    pub data: G::ProcessData,
}

/// An identifier within a [`ScheduleGraph`].
pub trait GraphNodeId:
    Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash + Debug + 'static
{
    /// Returns the index of the node into its sorted container in the graph.
    fn index(&self) -> usize;
}
