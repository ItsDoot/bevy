//! Traits used to define custom schedule graphs.

use alloc::{boxed::Box, vec::Vec};
use core::{error::Error, fmt::Debug, hash::Hash};

use crate::{
    component::Tick,
    schedule::{
        graph::Direction, InternedScheduleLabel, NodeConfig, NodeConfigs, ScheduleBuildPass,
        ScheduleExecutor,
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
    type BuildSettings: Default + Clone;
    /// The kind of executors supported by the graph.
    type ExecutorKind: Clone + Copy + PartialEq + Eq + Debug + Default;
    /// Metadata shared between all schedules of this type. Stored in
    /// [`Schedules`](crate::schedule2::Schedules).
    type GlobalMetadata: Clone + Default + Send + Sync + 'static;

    /// Creates a new executor of the given kind.
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
    fn update(
        &mut self,
        world: &mut World,
        executable: &mut Self::Executable,
        global_metadata: &Self::GlobalMetadata,
        label: InternedScheduleLabel,
    ) -> Result<(), Self::BuildError>;
}

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

/// Trait for types that can be converted into a [`NodeConfig`] with additional
/// metadata.
pub trait NodeType: Sized {
    /// Additional data used to configure a node.
    type Metadata;
    /// Additional data used to configure a group of nodes.
    type GroupMetadata: Default;

    /// Converts this node into a configuration.
    fn into_config(self) -> NodeConfig<Self>;
}

/// Trait for nodes to define how they get processed by a [`ScheduleGraph`].
pub trait GraphNode<G: ScheduleGraph>: NodeType {
    /// Extra data returned when processing a group of nodes.
    type ProcessData;

    /// Processes a single node of this type and adds it to the graph.
    fn process_config(graph: &mut G, config: NodeConfig<Self>) -> Result<G::Id, G::BuildError>;

    /// Processes one or more nodes of this type and adds them to the graph.
    fn process_configs(
        graph: &mut G,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, G>, G::BuildError>;
}

/// Result of calling [`GraphNode::process_configs`].
pub struct ProcessedConfigs<N: GraphNode<G>, G: ScheduleGraph> {
    /// The nodes that were processed.
    pub nodes: Vec<G::Id>,
    /// Extra data returned from processing the nodes.
    pub data: N::ProcessData,
}

/// Trait for types that can be used as unique identifiers in a [`DiGraph`] or
/// [`UnGraph`].
///
/// [`DiGraph`]: crate::schedule::graph::DiGraph
/// [`UnGraph`]: crate::schedule::graph::UnGraph
pub trait GraphNodeId: Copy + Eq + Ord + Hash + Debug + 'static {
    /// The type of pair of identifiers used to represent an edge in the graph.
    type Pair: GraphNodeIdPair<Self>;
    /// The type of directed identifier used to represent a directed edge in the graph.
    type Directed: DirectedGraphNodeId<Self>;
}

/// Trait for types that hold a pair of [`GraphNodeId`]s. Typically stored in a
/// memory-efficient way.
pub trait GraphNodeIdPair<Id: GraphNodeId>: Copy + Eq + Hash {
    /// Creates a new pair of identifiers.
    fn new(a: Id, b: Id) -> Self;

    /// Unpacks the pair into its components.
    fn unpack(self) -> (Id, Id);
}

impl<Id: GraphNodeId> GraphNodeIdPair<Id> for (Id, Id) {
    fn new(a: Id, b: Id) -> Self {
        (a, b)
    }

    fn unpack(self) -> (Id, Id) {
        self
    }
}

/// Trait for types that hold a [`GraphNodeId`] and a [`Direction`]. Typically
/// stored in a memory-efficient way.
pub trait DirectedGraphNodeId<Id: GraphNodeId>: Copy + Debug {
    /// Creates a new directed identifier.
    fn new(node: Id, direction: Direction) -> Self;

    /// Unpacks the directed identifier into its components.
    fn unpack(self) -> (Id, Direction);
}

impl<Id: GraphNodeId> DirectedGraphNodeId<Id> for (Id, Direction) {
    fn new(node: Id, direction: Direction) -> Self {
        (node, direction)
    }

    fn unpack(self) -> (Id, Direction) {
        self
    }
}
