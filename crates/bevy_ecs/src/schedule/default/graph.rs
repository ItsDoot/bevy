use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::{any::TypeId, fmt::Write as _};
use derive_more::derive::{Deref, DerefMut};

use bevy_platform_support::collections::{HashMap, HashSet};
use disqualified::ShortName;
use fixedbitset::FixedBitSet;
use log::{error, warn};
use thiserror::Error;

use crate::{
    component::{ComponentId, Components},
    query::AccessConflicts,
    schedule::{
        default::{
            DefaultGraphExecutable, DefaultGroupMetadata, DefaultMetadata, DenselyChained,
            GraphInfo, NodeId, ScheduledSystem,
        },
        graph::{
            check_graph, index, toposort_graph, CheckGraphResults, Dag, DiGraph, Direction::*,
            UnGraph,
        },
        pass::ScheduleBuildPassObj,
        passes::AutoInsertApplyDeferredPass,
        traits::{GraphNode, GraphNodeId, ProcessedConfigs, ScheduleGraph},
        Ambiguities, AnonymousSet, BoxedCondition, Chain, Dependencies, Dependency, DependencyKind,
        ExecutorKind, FallibleSystem, Hierarchy, InternedScheduleLabel, InternedSystemSet,
        MultiThreadedExecutor, NodeConfig, NodeConfigs, ScheduleBuildPass, ScheduleExecutor,
        SimpleExecutor, SingleThreadedExecutor, SystemSet,
    },
    storage::SparseSetIndex,
    world::World,
};

/// Metadata for a [`Schedule`].
///
/// The order isn't optimized; calling `ScheduleGraph::build_schedule` will return a
/// `SystemSchedule` where the order is optimized for execution.
#[derive(Default)]
pub struct DefaultGraph {
    /// List of systems in the schedule
    pub systems: Vec<SystemNode>,
    /// List of conditions for each system, in the same order as `systems`
    pub system_conditions: Vec<Vec<BoxedCondition>>,
    /// List of system sets in the schedule
    system_sets: Vec<SystemSetNode>,
    /// List of conditions for each system set, in the same order as `system_sets`
    system_set_conditions: Vec<Vec<BoxedCondition>>,
    /// Map from system set to node id
    pub(crate) system_set_ids: HashMap<InternedSystemSet, NodeId>,
    /// Systems that have not been initialized yet; for system sets, we store the index of the first uninitialized condition
    /// (all the conditions after that index still need to be initialized)
    uninit: Vec<(NodeId, usize)>,
    /// Directed acyclic graph of the hierarchy (which systems/sets are children of which sets)
    hierarchy: Dag<NodeId>,
    /// Directed acyclic graph of the dependency (which systems/sets have to run before which other systems/sets)
    dependency: Dag<NodeId>,
    pub(crate) ambiguous_with: UnGraph<NodeId>,
    /// Nodes that are allowed to have ambiguous ordering relationship with any other systems.
    pub ambiguous_with_all: HashSet<NodeId>,
    conflicting_systems: Vec<(NodeId, NodeId, Vec<ComponentId>)>,
    anonymous_sets: usize,
    changed: bool,
    settings: DefaultBuildSettings,
    passes: BTreeMap<TypeId, Box<dyn ScheduleBuildPassObj<Self>>>,
}

impl DefaultGraph {
    /// Creates an empty [`ScheduleGraph`] with default settings.
    pub fn new() -> Self {
        Self {
            systems: Vec::new(),
            system_conditions: Vec::new(),
            system_sets: Vec::new(),
            system_set_conditions: Vec::new(),
            system_set_ids: HashMap::default(),
            uninit: Vec::new(),
            hierarchy: Dag::default(),
            dependency: Dag::default(),
            ambiguous_with: UnGraph::default(),
            ambiguous_with_all: HashSet::default(),
            conflicting_systems: Vec::new(),
            anonymous_sets: 0,
            changed: false,
            settings: DefaultBuildSettings::default(),
            passes: BTreeMap::default(),
        }
    }

    /// Returns the system at the given [`NodeId`], if it exists.
    pub fn get_system_at(&self, id: NodeId) -> Option<&ScheduledSystem> {
        if !id.is_system() {
            return None;
        }
        self.systems
            .get(id.index())
            .and_then(|system| system.inner.as_ref())
    }

    /// Returns `true` if the given system set is part of the graph. Otherwise, returns `false`.
    pub fn contains_set(&self, set: impl SystemSet) -> bool {
        self.system_set_ids.contains_key(&set.intern())
    }

    /// Returns the system at the given [`NodeId`].
    ///
    /// Panics if it doesn't exist.
    #[track_caller]
    pub fn system_at(&self, id: NodeId) -> &ScheduledSystem {
        self.get_system_at(id)
            .ok_or_else(|| format!("system with id {id:?} does not exist in this Schedule"))
            .unwrap()
    }

    /// Returns the set at the given [`NodeId`], if it exists.
    pub fn get_set_at(&self, id: NodeId) -> Option<&dyn SystemSet> {
        if !id.is_set() {
            return None;
        }
        self.system_sets.get(id.index()).map(|set| &*set.inner)
    }

    /// Returns the set at the given [`NodeId`].
    ///
    /// Panics if it doesn't exist.
    #[track_caller]
    pub fn set_at(&self, id: NodeId) -> &dyn SystemSet {
        self.get_set_at(id)
            .ok_or_else(|| format!("set with id {id:?} does not exist in this Schedule"))
            .unwrap()
    }

    /// Returns the conditions for the set at the given [`NodeId`], if it exists.
    pub fn get_set_conditions_at(&self, id: NodeId) -> Option<&[BoxedCondition]> {
        if !id.is_set() {
            return None;
        }

        self.system_set_conditions
            .get(id.index())
            .map(Vec::as_slice)
    }

    /// Returns the conditions for the set at the given [`NodeId`].
    ///
    /// Panics if it doesn't exist.
    #[track_caller]
    pub fn set_conditions_at(&self, id: NodeId) -> &[BoxedCondition] {
        self.get_set_conditions_at(id)
            .ok_or_else(|| format!("set with id {id:?} does not exist in this Schedule"))
            .unwrap()
    }

    /// Returns an iterator over all systems in this schedule, along with the conditions for each system.
    pub fn systems(&self) -> impl Iterator<Item = (NodeId, &ScheduledSystem, &[BoxedCondition])> {
        self.systems
            .iter()
            .zip(self.system_conditions.iter())
            .enumerate()
            .filter_map(|(i, (system_node, condition))| {
                let system = system_node.inner.as_ref()?;
                Some((NodeId::System(i), system, condition.as_slice()))
            })
    }

    /// Returns an iterator over all system sets in this schedule, along with the conditions for each
    /// system set.
    pub fn system_sets(&self) -> impl Iterator<Item = (NodeId, &dyn SystemSet, &[BoxedCondition])> {
        self.system_set_ids.iter().map(|(_, &node_id)| {
            let set_node = &self.system_sets[node_id.index()];
            let set = &*set_node.inner;
            let conditions = self.system_set_conditions[node_id.index()].as_slice();
            (node_id, set, conditions)
        })
    }

    /// Returns the [`Dag`] of the hierarchy.
    ///
    /// The hierarchy is a directed acyclic graph of the systems and sets,
    /// where an edge denotes that a system or set is the child of another set.
    pub fn hierarchy(&self) -> &Dag<NodeId> {
        &self.hierarchy
    }

    /// Returns the [`Dag`] of the dependencies in the schedule.
    ///
    /// Nodes in this graph are systems and sets, and edges denote that
    /// a system or set has to run before another system or set.
    pub fn dependency(&self) -> &Dag<NodeId> {
        &self.dependency
    }

    /// Returns the list of systems that conflict with each other, i.e. have ambiguities in their access.
    ///
    /// If the `Vec<ComponentId>` is empty, the systems conflict on [`World`] access.
    /// Must be called after [`ScheduleGraph::build_schedule`] to be non-empty.
    pub fn conflicting_systems(&self) -> &[(NodeId, NodeId, Vec<ComponentId>)] {
        &self.conflicting_systems
    }

    fn apply_collective_conditions<N>(
        &mut self,
        configs: &mut [NodeConfigs<N, Self>],
        collective_conditions: Vec<BoxedCondition>,
    ) where
        N: GraphNode<Self, Metadata = DefaultMetadata, GroupMetadata = DefaultGroupMetadata>,
    {
        if !collective_conditions.is_empty() {
            if let [config] = configs {
                for condition in collective_conditions {
                    config.run_if_dyn(condition);
                }
            } else {
                let set = self.create_anonymous_set();
                for config in configs.iter_mut() {
                    config.in_set_inner(set.intern());
                }
                let mut set_config = set.intern().into_config();
                set_config.metadata.conditions.extend(collective_conditions);
                self.configure_set_inner(set_config).unwrap();
            }
        }
    }

    /// Adds the config nodes to the graph.
    ///
    /// `collect_nodes` controls whether the `NodeId`s of the processed config nodes are stored in the returned [`ProcessConfigsResult`].
    /// `process_config` is the function which processes each individual config node and returns a corresponding `NodeId`.
    ///
    /// The fields on the returned [`ProcessConfigsResult`] are:
    /// - `nodes`: a vector of all node ids contained in the nested `NodeConfigs`
    /// - `densely_chained`: a boolean that is true if all nested nodes are linearly chained (with successive `after` orderings) in the order they are defined
    #[track_caller]
    pub(crate) fn process_configs<N>(
        &mut self,
        configs: NodeConfigs<N, Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<N, Self>, DefaultBuildError>
    where
        N: GraphNode<
            Self,
            Metadata = DefaultMetadata,
            GroupMetadata = DefaultGroupMetadata,
            ProcessData = DenselyChained,
        >,
    {
        match configs {
            NodeConfigs::Single(config) => Ok(ProcessedConfigs {
                nodes: collect_nodes
                    .then_some(N::process_config(self, config)?)
                    .into_iter()
                    .collect(),
                data: DenselyChained(true),
            }),
            NodeConfigs::Group {
                mut configs,
                metadata,
            } => {
                self.apply_collective_conditions(&mut configs, metadata.collective_conditions.0);

                let is_chained = matches!(metadata.chained, Chain::Chained(_));

                // Densely chained if
                // * chained and all configs in the chain are densely chained, or
                // * unchained with a single densely chained config
                let mut densely_chained = is_chained || configs.len() == 1;
                let mut configs = configs.into_iter();
                let mut nodes = Vec::new();

                let Some(first) = configs.next() else {
                    return Ok(ProcessedConfigs {
                        nodes: Vec::new(),
                        data: DenselyChained(densely_chained),
                    });
                };
                let mut previous_result =
                    self.process_configs(first, collect_nodes || is_chained)?;
                densely_chained &= previous_result.data.0;

                for current in configs {
                    let current_result =
                        self.process_configs(current, collect_nodes || is_chained)?;
                    densely_chained &= current_result.data.0;

                    if let Chain::Chained(chain_options) = &metadata.chained {
                        // if the current result is densely chained, we only need to chain the first node
                        let current_nodes = if current_result.data.0 {
                            &current_result.nodes[..1]
                        } else {
                            &current_result.nodes
                        };
                        // if the previous result was densely chained, we only need to chain the last node
                        let previous_nodes = if previous_result.data.0 {
                            &previous_result.nodes[previous_result.nodes.len() - 1..]
                        } else {
                            &previous_result.nodes
                        };

                        for previous_node in previous_nodes {
                            for current_node in current_nodes {
                                self.dependency
                                    .graph
                                    .add_edge(*previous_node, *current_node);

                                for pass in self.passes.values_mut() {
                                    pass.add_dependency(
                                        *previous_node,
                                        *current_node,
                                        chain_options,
                                    );
                                }
                            }
                        }
                    }
                    if collect_nodes {
                        nodes.append(&mut previous_result.nodes);
                    }

                    previous_result = current_result;
                }
                if collect_nodes {
                    nodes.append(&mut previous_result.nodes);
                }

                Ok(ProcessedConfigs {
                    nodes,
                    data: DenselyChained(densely_chained),
                })
            }
        }
    }

    /// Add a [`SystemConfig`] to the graph, including its dependencies and conditions.
    pub(crate) fn add_system_inner(
        &mut self,
        config: NodeConfig<FallibleSystem, Self>,
    ) -> Result<NodeId, DefaultBuildError> {
        let id = NodeId::System(self.systems.len());

        // graph updates are immediate
        self.update_graphs(id, config.metadata.graph_info)?;

        // system init has to be deferred (need `&mut World`)
        self.uninit.push((id, 0));
        self.systems.push(SystemNode::new(config.node.0));
        self.system_conditions.push(config.metadata.conditions.0);

        Ok(id)
    }

    /// Add a single `SystemSetConfig` to the graph, including its dependencies and conditions.
    pub(crate) fn configure_set_inner(
        &mut self,
        mut config: NodeConfig<InternedSystemSet, Self>,
    ) -> Result<NodeId, DefaultBuildError> {
        let id = match self.system_set_ids.get(&config.node) {
            Some(&id) => id,
            None => self.add_set(config.node),
        };

        // graph updates are immediate
        self.update_graphs(id, config.metadata.graph_info)?;

        // system init has to be deferred (need `&mut World`)
        let system_set_conditions = &mut self.system_set_conditions[id.index()];
        self.uninit.push((id, system_set_conditions.len()));
        system_set_conditions.append(&mut config.metadata.conditions.0);

        Ok(id)
    }

    fn add_set(&mut self, set: InternedSystemSet) -> NodeId {
        let id = NodeId::Set(self.system_sets.len());
        self.system_sets.push(SystemSetNode::new(set));
        self.system_set_conditions.push(Vec::new());
        self.system_set_ids.insert(set, id);
        id
    }

    /// Checks that a system set isn't included in itself.
    /// If not present, add the set to the graph.
    fn check_hierarchy_set(
        &mut self,
        id: &NodeId,
        set: InternedSystemSet,
    ) -> Result<(), DefaultBuildError> {
        match self.system_set_ids.get(&set) {
            Some(set_id) => {
                if id == set_id {
                    return Err(DefaultBuildError::HierarchyLoop(self.node_name(*id)));
                }
            }
            None => {
                self.add_set(set);
            }
        }

        Ok(())
    }

    fn create_anonymous_set(&mut self) -> AnonymousSet {
        let id = self.anonymous_sets;
        self.anonymous_sets += 1;
        AnonymousSet::new(id)
    }

    /// Check that no set is included in itself.
    /// Add all the sets from the [`GraphInfo`]'s hierarchy to the graph.
    fn check_hierarchy_sets(
        &mut self,
        id: &NodeId,
        hierarchy: &Hierarchy<InternedSystemSet>,
    ) -> Result<(), DefaultBuildError> {
        for &set in &hierarchy.0 {
            self.check_hierarchy_set(id, set)?;
        }

        Ok(())
    }

    /// Checks that no system set is dependent on itself.
    /// Add all the sets from the [`GraphInfo`]'s dependencies to the graph.
    fn check_edges(
        &mut self,
        id: &NodeId,
        dependencies: &Dependencies<InternedSystemSet>,
        ambiguities: &Ambiguities<InternedSystemSet>,
    ) -> Result<(), DefaultBuildError> {
        for Dependency { target: set, .. } in &dependencies.0 {
            match self.system_set_ids.get(set) {
                Some(set_id) => {
                    if id == set_id {
                        return Err(DefaultBuildError::DependencyLoop(self.node_name(*id)));
                    }
                }
                None => {
                    self.add_set(*set);
                }
            }
        }

        if let Ambiguities::IgnoreAnyFrom(ambiguous_with) = &ambiguities {
            for set in ambiguous_with {
                if !self.system_set_ids.contains_key(set) {
                    self.add_set(*set);
                }
            }
        }

        Ok(())
    }

    /// Update the internal graphs (hierarchy, dependency, ambiguity) by adding a single [`GraphInfo`]
    fn update_graphs(
        &mut self,
        id: NodeId,
        graph_info: GraphInfo,
    ) -> Result<(), DefaultBuildError> {
        self.check_hierarchy_sets(&id, &graph_info.hierarchy)?;
        self.check_edges(&id, &graph_info.dependencies, &graph_info.ambiguous_with)?;
        self.changed = true;

        let GraphInfo {
            hierarchy: sets,
            dependencies,
            ambiguous_with,
            ..
        } = graph_info;

        self.hierarchy.graph.add_node(id);
        self.dependency.graph.add_node(id);

        for set in sets.0.into_iter().map(|set| self.system_set_ids[&set]) {
            self.hierarchy.graph.add_edge(set, id);

            // ensure set also appears in dependency graph
            self.dependency.graph.add_node(set);
        }

        for (kind, set, options) in dependencies.0.into_iter().map(
            |Dependency {
                 kind,
                 target: set,
                 options,
             }| (kind, self.system_set_ids[&set], options),
        ) {
            let (lhs, rhs) = match kind {
                DependencyKind::Before => (id, set),
                DependencyKind::After => (set, id),
            };
            self.dependency.graph.add_edge(lhs, rhs);
            for pass in self.passes.values_mut() {
                pass.add_dependency(lhs, rhs, &options);
            }

            // ensure set also appears in hierarchy graph
            self.hierarchy.graph.add_node(set);
        }

        match ambiguous_with {
            Ambiguities::Check => (),
            Ambiguities::IgnoreAnyFrom(ambiguous_with) => {
                for set in ambiguous_with
                    .into_iter()
                    .map(|set| self.system_set_ids[&set])
                {
                    self.ambiguous_with.add_edge(id, set);
                }
            }
            Ambiguities::IgnoreAll => {
                self.ambiguous_with_all.insert(id);
            }
        }

        Ok(())
    }

    /// Build a [`SystemSchedule`] optimized for scheduler access from the [`ScheduleGraph`].
    ///
    /// This method also
    /// - checks for dependency or hierarchy cycles
    /// - checks for system access conflicts and reports ambiguities
    pub fn build_schedule(
        &mut self,
        world: &mut World,
        schedule_label: InternedScheduleLabel,
        ignored_ambiguities: &BTreeSet<ComponentId>,
    ) -> Result<DefaultGraphExecutable, DefaultBuildError> {
        // check hierarchy for cycles
        self.hierarchy.topsort = toposort_graph(&self.hierarchy.graph)
            .map_err(|e| DefaultBuildError::HierarchyCycle(e.hierarchy_cycle(self)))?;

        let hier_results = check_graph(&self.hierarchy.graph, &self.hierarchy.topsort);
        self.optionally_check_hierarchy_conflicts(&hier_results.transitive_edges, schedule_label)?;

        // remove redundant edges
        self.hierarchy.graph = hier_results.transitive_reduction;

        // check dependencies for cycles
        self.dependency.topsort = toposort_graph(&self.dependency.graph)
            .map_err(|e| DefaultBuildError::DependencyCycle(e.dependency_cycle(self)))?;

        // check for systems or system sets depending on sets they belong to
        let dep_results = check_graph(&self.dependency.graph, &self.dependency.topsort);
        self.check_for_cross_dependencies(&dep_results, &hier_results.connected)?;

        // map all system sets to their systems
        // go in reverse topological order (bottom-up) for efficiency
        let (set_systems, set_system_bitsets) =
            self.map_sets_to_systems(&self.hierarchy.topsort, &self.hierarchy.graph);
        self.check_order_but_intersect(&dep_results.connected, &set_system_bitsets)?;

        // check that there are no edges to system-type sets that have multiple instances
        self.check_system_type_set_ambiguity(&set_systems)?;

        let mut dependency_flattened = self.get_dependency_flattened(&set_systems);

        // modify graph with build passes
        let mut passes = core::mem::take(&mut self.passes);
        for pass in passes.values_mut() {
            pass.build(world, self, &mut dependency_flattened)?;
        }
        self.passes = passes;

        // topsort
        let mut dependency_flattened_dag = Dag {
            topsort: toposort_graph(&dependency_flattened)
                .map_err(|e| DefaultBuildError::DependencyCycle(e.dependency_cycle(self)))?,
            graph: dependency_flattened,
        };

        let flat_results = check_graph(
            &dependency_flattened_dag.graph,
            &dependency_flattened_dag.topsort,
        );

        // remove redundant edges
        dependency_flattened_dag.graph = flat_results.transitive_reduction;

        // flatten: combine `in_set` with `ambiguous_with` information
        let ambiguous_with_flattened = self.get_ambiguous_with_flattened(&set_systems);

        // check for conflicts
        let conflicting_systems = self.get_conflicting_systems(
            &flat_results.disconnected,
            &ambiguous_with_flattened,
            ignored_ambiguities,
        );
        self.optionally_check_conflicts(&conflicting_systems, world.components(), schedule_label)?;
        self.conflicting_systems = conflicting_systems;

        // build the schedule
        Ok(self.build_schedule_inner(dependency_flattened_dag, hier_results.reachable))
    }

    /// Return a map from system set `NodeId` to a list of system `NodeId`s that are included in the set.
    /// Also return a map from system set `NodeId` to a `FixedBitSet` of system `NodeId`s that are included in the set,
    /// where the bitset order is the same as `self.systems`
    fn map_sets_to_systems(
        &self,
        hierarchy_topsort: &[NodeId],
        hierarchy_graph: &DiGraph<NodeId>,
    ) -> (HashMap<NodeId, Vec<NodeId>>, HashMap<NodeId, FixedBitSet>) {
        let mut set_systems: HashMap<NodeId, Vec<NodeId>> =
            HashMap::with_capacity_and_hasher(self.system_sets.len(), Default::default());
        let mut set_system_bitsets =
            HashMap::with_capacity_and_hasher(self.system_sets.len(), Default::default());
        for &id in hierarchy_topsort.iter().rev() {
            if id.is_system() {
                continue;
            }

            let mut systems = Vec::new();
            let mut system_bitset = FixedBitSet::with_capacity(self.systems.len());

            for child in hierarchy_graph.neighbors_directed(id, Outgoing) {
                match child {
                    NodeId::System(_) => {
                        systems.push(child);
                        system_bitset.insert(child.index());
                    }
                    NodeId::Set(_) => {
                        let child_systems = set_systems.get(&child).unwrap();
                        let child_system_bitset = set_system_bitsets.get(&child).unwrap();
                        systems.extend_from_slice(child_systems);
                        system_bitset.union_with(child_system_bitset);
                    }
                }
            }

            set_systems.insert(id, systems);
            set_system_bitsets.insert(id, system_bitset);
        }
        (set_systems, set_system_bitsets)
    }

    fn get_dependency_flattened(
        &mut self,
        set_systems: &HashMap<NodeId, Vec<NodeId>>,
    ) -> DiGraph<NodeId> {
        // flatten: combine `in_set` with `before` and `after` information
        // have to do it like this to preserve transitivity
        let mut dependency_flattened = self.dependency.graph.clone();
        let mut temp = Vec::new();
        for (&set, systems) in set_systems {
            for pass in self.passes.values_mut() {
                pass.collapse_set(set, systems, &dependency_flattened, &mut temp);
            }
            if systems.is_empty() {
                // collapse dependencies for empty sets
                for a in dependency_flattened.neighbors_directed(set, Incoming) {
                    for b in dependency_flattened.neighbors_directed(set, Outgoing) {
                        temp.push((a, b));
                    }
                }
            } else {
                for a in dependency_flattened.neighbors_directed(set, Incoming) {
                    for &sys in systems {
                        temp.push((a, sys));
                    }
                }

                for b in dependency_flattened.neighbors_directed(set, Outgoing) {
                    for &sys in systems {
                        temp.push((sys, b));
                    }
                }
            }

            dependency_flattened.remove_node(set);
            for (a, b) in temp.drain(..) {
                dependency_flattened.add_edge(a, b);
            }
        }

        dependency_flattened
    }

    fn get_ambiguous_with_flattened(
        &self,
        set_systems: &HashMap<NodeId, Vec<NodeId>>,
    ) -> UnGraph<NodeId> {
        let mut ambiguous_with_flattened = UnGraph::default();
        for (lhs, rhs) in self.ambiguous_with.all_edges() {
            match (lhs, rhs) {
                (NodeId::System(_), NodeId::System(_)) => {
                    ambiguous_with_flattened.add_edge(lhs, rhs);
                }
                (NodeId::Set(_), NodeId::System(_)) => {
                    for &lhs_ in set_systems.get(&lhs).unwrap_or(&Vec::new()) {
                        ambiguous_with_flattened.add_edge(lhs_, rhs);
                    }
                }
                (NodeId::System(_), NodeId::Set(_)) => {
                    for &rhs_ in set_systems.get(&rhs).unwrap_or(&Vec::new()) {
                        ambiguous_with_flattened.add_edge(lhs, rhs_);
                    }
                }
                (NodeId::Set(_), NodeId::Set(_)) => {
                    for &lhs_ in set_systems.get(&lhs).unwrap_or(&Vec::new()) {
                        for &rhs_ in set_systems.get(&rhs).unwrap_or(&vec![]) {
                            ambiguous_with_flattened.add_edge(lhs_, rhs_);
                        }
                    }
                }
            }
        }

        ambiguous_with_flattened
    }

    fn get_conflicting_systems(
        &self,
        flat_results_disconnected: &Vec<(NodeId, NodeId)>,
        ambiguous_with_flattened: &UnGraph<NodeId>,
        ignored_ambiguities: &BTreeSet<ComponentId>,
    ) -> Vec<(NodeId, NodeId, Vec<ComponentId>)> {
        let mut conflicting_systems = Vec::new();
        for &(a, b) in flat_results_disconnected {
            if ambiguous_with_flattened.contains_edge(a, b)
                || self.ambiguous_with_all.contains(&a)
                || self.ambiguous_with_all.contains(&b)
            {
                continue;
            }

            let system_a = self.systems[a.index()].get().unwrap();
            let system_b = self.systems[b.index()].get().unwrap();
            if system_a.is_exclusive() || system_b.is_exclusive() {
                conflicting_systems.push((a, b, Vec::new()));
            } else {
                let access_a = system_a.component_access();
                let access_b = system_b.component_access();
                if !access_a.is_compatible(access_b) {
                    match access_a.get_conflicts(access_b) {
                        AccessConflicts::Individual(conflicts) => {
                            let conflicts: Vec<_> = conflicts
                                .ones()
                                .map(ComponentId::get_sparse_set_index)
                                .filter(|id| !ignored_ambiguities.contains(id))
                                .collect();
                            if !conflicts.is_empty() {
                                conflicting_systems.push((a, b, conflicts));
                            }
                        }
                        AccessConflicts::All => {
                            // there is no specific component conflicting, but the systems are overall incompatible
                            // for example 2 systems with `Query<EntityMut>`
                            conflicting_systems.push((a, b, Vec::new()));
                        }
                    }
                }
            }
        }

        conflicting_systems
    }

    fn build_schedule_inner(
        &self,
        dependency_flattened_dag: Dag<NodeId>,
        hier_results_reachable: FixedBitSet,
    ) -> DefaultGraphExecutable {
        let dg_system_ids = dependency_flattened_dag.topsort.clone();
        let dg_system_idx_map = dg_system_ids
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, id)| (id, i))
            .collect::<HashMap<_, _>>();

        let hg_systems = self
            .hierarchy
            .topsort
            .iter()
            .cloned()
            .enumerate()
            .filter(|&(_i, id)| id.is_system())
            .collect::<Vec<_>>();

        let (hg_set_with_conditions_idxs, hg_set_ids): (Vec<_>, Vec<_>) = self
            .hierarchy
            .topsort
            .iter()
            .cloned()
            .enumerate()
            .filter(|&(_i, id)| {
                // ignore system sets that have no conditions
                // ignore system type sets (already covered, they don't have conditions)
                id.is_set() && !self.system_set_conditions[id.index()].is_empty()
            })
            .unzip();

        let sys_count = self.systems.len();
        let set_with_conditions_count = hg_set_ids.len();
        let hg_node_count = self.hierarchy.graph.node_count();

        // get the number of dependencies and the immediate dependents of each system
        // (needed by multi_threaded executor to run systems in the correct order)
        let mut system_dependencies = Vec::with_capacity(sys_count);
        let mut system_dependents = Vec::with_capacity(sys_count);
        for &sys_id in &dg_system_ids {
            let num_dependencies = dependency_flattened_dag
                .graph
                .neighbors_directed(sys_id, Incoming)
                .count();

            let dependents = dependency_flattened_dag
                .graph
                .neighbors_directed(sys_id, Outgoing)
                .map(|dep_id| dg_system_idx_map[&dep_id])
                .collect::<Vec<_>>();

            system_dependencies.push(num_dependencies);
            system_dependents.push(dependents);
        }

        // get the rows and columns of the hierarchy graph's reachability matrix
        // (needed to we can evaluate conditions in the correct order)
        let mut systems_in_sets_with_conditions =
            vec![FixedBitSet::with_capacity(sys_count); set_with_conditions_count];
        for (i, &row) in hg_set_with_conditions_idxs.iter().enumerate() {
            let bitset = &mut systems_in_sets_with_conditions[i];
            for &(col, sys_id) in &hg_systems {
                let idx = dg_system_idx_map[&sys_id];
                let is_descendant = hier_results_reachable[index(row, col, hg_node_count)];
                bitset.set(idx, is_descendant);
            }
        }

        let mut sets_with_conditions_of_systems =
            vec![FixedBitSet::with_capacity(set_with_conditions_count); sys_count];
        for &(col, sys_id) in &hg_systems {
            let i = dg_system_idx_map[&sys_id];
            let bitset = &mut sets_with_conditions_of_systems[i];
            for (idx, &row) in hg_set_with_conditions_idxs
                .iter()
                .enumerate()
                .take_while(|&(_idx, &row)| row < col)
            {
                let is_ancestor = hier_results_reachable[index(row, col, hg_node_count)];
                bitset.set(idx, is_ancestor);
            }
        }

        DefaultGraphExecutable {
            systems: Vec::with_capacity(sys_count),
            system_conditions: Vec::with_capacity(sys_count),
            set_conditions: Vec::with_capacity(set_with_conditions_count),
            system_ids: dg_system_ids,
            set_ids: hg_set_ids,
            system_dependencies,
            system_dependents,
            sets_with_conditions_of_systems,
            systems_in_sets_with_conditions,
        }
    }
}

// methods for reporting errors
impl DefaultGraph {
    #[inline]
    fn get_node_name_inner(&self, id: &NodeId, report_sets: bool) -> String {
        let name = match id {
            NodeId::System(_) => {
                let name = self.systems[id.index()].get().unwrap().name().to_string();
                if report_sets {
                    let sets = self.names_of_sets_containing_node(id);
                    if sets.is_empty() {
                        name
                    } else if sets.len() == 1 {
                        format!("{name} (in set {})", sets[0])
                    } else {
                        format!("{name} (in sets {})", sets.join(", "))
                    }
                } else {
                    name
                }
            }
            NodeId::Set(_) => {
                let set = &self.system_sets[id.index()];
                if set.is_anonymous() {
                    self.anonymous_set_name(id)
                } else {
                    set.name()
                }
            }
        };
        if self.settings.use_shortnames {
            ShortName(&name).to_string()
        } else {
            name
        }
    }

    fn anonymous_set_name(&self, id: &NodeId) -> String {
        format!(
            "({})",
            self.hierarchy
                .graph
                .edges_directed(*id, Outgoing)
                // never get the sets of the members or this will infinite recurse when the report_sets setting is on.
                .map(|(_, member_id)| self.get_node_name_inner(&member_id, false))
                .reduce(|a, b| format!("{a}, {b}"))
                .unwrap_or_default()
        )
    }

    /// If [`ScheduleBuildSettings::hierarchy_detection`] is [`LogLevel::Ignore`] this check
    /// is skipped.
    fn optionally_check_hierarchy_conflicts(
        &self,
        transitive_edges: &[(NodeId, NodeId)],
        schedule_label: InternedScheduleLabel,
    ) -> Result<(), DefaultBuildError> {
        if self.settings.hierarchy_detection == LogLevel::Ignore || transitive_edges.is_empty() {
            return Ok(());
        }

        let message = self.get_hierarchy_conflicts_error_message(transitive_edges);
        match self.settings.hierarchy_detection {
            LogLevel::Ignore => unreachable!(),
            LogLevel::Warn => {
                error!(
                    "Schedule {schedule_label:?} has redundant edges:\n {}",
                    message
                );
                Ok(())
            }
            LogLevel::Error => Err(DefaultBuildError::HierarchyRedundancy(message)),
        }
    }

    fn get_hierarchy_conflicts_error_message(
        &self,
        transitive_edges: &[(NodeId, NodeId)],
    ) -> String {
        let mut message = String::from("hierarchy contains redundant edge(s)");
        for (parent, child) in transitive_edges {
            writeln!(
                message,
                " -- {} `{}` cannot be child of set `{}`, longer path exists",
                child.kind(),
                self.node_name(*child),
                self.node_name(*parent),
            )
            .unwrap();
        }

        message
    }

    fn check_for_cross_dependencies(
        &self,
        dep_results: &CheckGraphResults<NodeId>,
        hier_results_connected: &HashSet<(NodeId, NodeId)>,
    ) -> Result<(), DefaultBuildError> {
        for &(a, b) in &dep_results.connected {
            if hier_results_connected.contains(&(a, b)) || hier_results_connected.contains(&(b, a))
            {
                let name_a = self.node_name(a);
                let name_b = self.node_name(b);
                return Err(DefaultBuildError::CrossDependency(name_a, name_b));
            }
        }

        Ok(())
    }

    fn check_order_but_intersect(
        &self,
        dep_results_connected: &HashSet<(NodeId, NodeId)>,
        set_system_bitsets: &HashMap<NodeId, FixedBitSet>,
    ) -> Result<(), DefaultBuildError> {
        // check that there is no ordering between system sets that intersect
        for (a, b) in dep_results_connected {
            if !(a.is_set() && b.is_set()) {
                continue;
            }

            let a_systems = set_system_bitsets.get(a).unwrap();
            let b_systems = set_system_bitsets.get(b).unwrap();

            if !a_systems.is_disjoint(b_systems) {
                return Err(DefaultBuildError::SetsHaveOrderButIntersect(
                    self.node_name(*a),
                    self.node_name(*b),
                ));
            }
        }

        Ok(())
    }

    fn check_system_type_set_ambiguity(
        &self,
        set_systems: &HashMap<NodeId, Vec<NodeId>>,
    ) -> Result<(), DefaultBuildError> {
        for (&id, systems) in set_systems {
            let set = &self.system_sets[id.index()];
            if set.is_system_type() {
                let instances = systems.len();
                let ambiguous_with = self.ambiguous_with.edges(id);
                let before = self.dependency.graph.edges_directed(id, Incoming);
                let after = self.dependency.graph.edges_directed(id, Outgoing);
                let relations = before.count() + after.count() + ambiguous_with.count();
                if instances > 1 && relations > 0 {
                    return Err(DefaultBuildError::SystemTypeSetAmbiguity(
                        self.node_name(id),
                    ));
                }
            }
        }
        Ok(())
    }

    /// if [`ScheduleBuildSettings::ambiguity_detection`] is [`LogLevel::Ignore`], this check is skipped
    fn optionally_check_conflicts(
        &self,
        conflicts: &[(NodeId, NodeId, Vec<ComponentId>)],
        components: &Components,
        schedule_label: InternedScheduleLabel,
    ) -> Result<(), DefaultBuildError> {
        if self.settings.ambiguity_detection == LogLevel::Ignore || conflicts.is_empty() {
            return Ok(());
        }

        let message = self.get_conflicts_error_message(conflicts, components);
        match self.settings.ambiguity_detection {
            LogLevel::Ignore => Ok(()),
            LogLevel::Warn => {
                warn!("Schedule {schedule_label:?} has ambiguities.\n{}", message);
                Ok(())
            }
            LogLevel::Error => Err(DefaultBuildError::Ambiguity(message)),
        }
    }

    fn get_conflicts_error_message(
        &self,
        ambiguities: &[(NodeId, NodeId, Vec<ComponentId>)],
        components: &Components,
    ) -> String {
        let n_ambiguities = ambiguities.len();

        let mut message = format!(
                "{n_ambiguities} pairs of systems with conflicting data access have indeterminate execution order. \
                Consider adding `before`, `after`, or `ambiguous_with` relationships between these:\n",
            );

        for (name_a, name_b, conflicts) in self.conflicts_to_string(ambiguities, components) {
            writeln!(message, " -- {name_a} and {name_b}").unwrap();

            if !conflicts.is_empty() {
                writeln!(message, "    conflict on: {conflicts:?}").unwrap();
            } else {
                // one or both systems must be exclusive
                let world = core::any::type_name::<World>();
                writeln!(message, "    conflict on: {world}").unwrap();
            }
        }

        message
    }

    /// convert conflicts to human readable format
    pub fn conflicts_to_string<'a>(
        &'a self,
        ambiguities: &'a [(NodeId, NodeId, Vec<ComponentId>)],
        components: &'a Components,
    ) -> impl Iterator<Item = (String, String, Vec<&'a str>)> + 'a {
        ambiguities
            .iter()
            .map(move |&(system_a, system_b, ref conflicts)| {
                let name_a = self.node_name(system_a);
                let name_b = self.node_name(system_b);

                debug_assert!(system_a.is_system(), "{name_a} is not a system.");
                debug_assert!(system_b.is_system(), "{name_b} is not a system.");

                let conflict_names: Vec<_> = conflicts
                    .iter()
                    .map(|id| components.get_name(*id).unwrap())
                    .collect();

                (name_a, name_b, conflict_names)
            })
    }

    fn traverse_sets_containing_node(&self, id: NodeId, f: &mut impl FnMut(NodeId) -> bool) {
        for (set_id, _) in self.hierarchy.graph.edges_directed(id, Incoming) {
            if f(set_id) {
                self.traverse_sets_containing_node(set_id, f);
            }
        }
    }

    fn names_of_sets_containing_node(&self, id: &NodeId) -> Vec<String> {
        let mut sets = <HashSet<_>>::default();
        self.traverse_sets_containing_node(*id, &mut |set_id| {
            !self.system_sets[set_id.index()].is_system_type() && sets.insert(set_id)
        });
        let mut sets: Vec<_> = sets
            .into_iter()
            .map(|set_id| self.node_name(set_id))
            .collect();
        sets.sort();
        sets
    }
}

impl ScheduleGraph for DefaultGraph {
    type Id = NodeId;
    type Executable = DefaultGraphExecutable;
    type BuildError = DefaultBuildError;
    type BuildSettings = DefaultBuildSettings;
    type ExecutorKind = ExecutorKind;
    type GlobalMetadata = IgnoredSchedulingAmbiguities;

    fn new_executor(kind: Self::ExecutorKind) -> Box<dyn ScheduleExecutor<Self>> {
        match kind {
            ExecutorKind::Simple => Box::new(SimpleExecutor::new()),
            ExecutorKind::SingleThreaded => Box::new(SingleThreadedExecutor::new()),
            #[cfg(feature = "std")]
            ExecutorKind::MultiThreaded => Box::new(MultiThreadedExecutor::new()),
        }
    }

    fn changed(&self) -> bool {
        self.changed
    }

    fn set_changed(&mut self, changed: bool) {
        self.changed = changed;
    }

    fn add_build_pass<P: ScheduleBuildPass<Self>>(&mut self, pass: P) {
        self.passes.insert(TypeId::of::<P>(), Box::new(pass));
    }

    fn remove_build_pass<P: ScheduleBuildPass<Self>>(&mut self) {
        self.passes.remove(&TypeId::of::<P>());
    }

    fn get_build_settings(&self) -> &Self::BuildSettings {
        &self.settings
    }

    fn set_build_settings(&mut self, settings: Self::BuildSettings) {
        if settings.auto_insert_apply_deferred {
            self.add_build_pass(AutoInsertApplyDeferredPass::default());
        } else {
            self.remove_build_pass::<AutoInsertApplyDeferredPass>();
        }
        self.settings = settings;
    }

    fn node_name(&self, node: Self::Id) -> String {
        self.get_node_name_inner(&node, self.settings.report_sets)
    }

    fn initialize(&mut self, world: &mut World) {
        for (id, i) in self.uninit.drain(..) {
            match id {
                NodeId::System(index) => {
                    self.systems[index].get_mut().unwrap().initialize(world);
                    for condition in &mut self.system_conditions[index] {
                        condition.initialize(world);
                    }
                }
                NodeId::Set(index) => {
                    for condition in self.system_set_conditions[index].iter_mut().skip(i) {
                        condition.initialize(world);
                    }
                }
            }
        }
    }

    fn update(
        &mut self,
        world: &mut World,
        executable: &mut Self::Executable,
        ignored_ambiguities: &Self::GlobalMetadata,
        label: InternedScheduleLabel,
    ) -> Result<(), Self::BuildError> {
        if !self.uninit.is_empty() {
            return Err(DefaultBuildError::Uninitialized);
        }

        // move systems out of old schedule
        for ((id, system), conditions) in executable
            .system_ids
            .drain(..)
            .zip(executable.systems.drain(..))
            .zip(executable.system_conditions.drain(..))
        {
            self.systems[id.index()].inner = Some(system);
            self.system_conditions[id.index()] = conditions;
        }

        for (id, conditions) in executable
            .set_ids
            .drain(..)
            .zip(executable.set_conditions.drain(..))
        {
            self.system_set_conditions[id.index()] = conditions;
        }

        *executable = self.build_schedule(world, label, ignored_ambiguities)?;

        // move systems into new schedule
        for &id in &executable.system_ids {
            let system = self.systems[id.index()].inner.take().unwrap();
            let conditions = core::mem::take(&mut self.system_conditions[id.index()]);
            executable.systems.push(system);
            executable.system_conditions.push(conditions);
        }

        for &id in &executable.set_ids {
            let conditions = core::mem::take(&mut self.system_set_conditions[id.index()]);
            executable.set_conditions.push(conditions);
        }

        Ok(())
    }
}

/// A [`ScheduledSystem`] stored in a [`ScheduleGraph`].
pub struct SystemNode {
    inner: Option<ScheduledSystem>,
}

impl SystemNode {
    /// Create a new [`SystemNode`]
    pub fn new(system: ScheduledSystem) -> Self {
        Self {
            inner: Some(system),
        }
    }

    /// Obtain a reference to the [`ScheduledSystem`] represented by this node.
    pub fn get(&self) -> Option<&ScheduledSystem> {
        self.inner.as_ref()
    }

    /// Obtain a mutable reference to the [`ScheduledSystem`] represented by this node.
    pub fn get_mut(&mut self) -> Option<&mut ScheduledSystem> {
        self.inner.as_mut()
    }
}

/// A [`SystemSet`] with metadata, stored in a [`ScheduleGraph`].
struct SystemSetNode {
    inner: InternedSystemSet,
}

impl SystemSetNode {
    pub fn new(set: InternedSystemSet) -> Self {
        Self { inner: set }
    }

    pub fn name(&self) -> String {
        format!("{:?}", &self.inner)
    }

    pub fn is_system_type(&self) -> bool {
        self.inner.system_type().is_some()
    }

    pub fn is_anonymous(&self) -> bool {
        self.inner.is_anonymous()
    }
}

/// Specifies miscellaneous settings for schedule construction.
#[derive(Clone, Debug)]
pub struct DefaultBuildSettings {
    /// Determines whether the presence of ambiguities (systems with conflicting access but indeterminate order)
    /// is only logged or also results in an [`Ambiguity`](ScheduleBuildError::Ambiguity) error.
    ///
    /// Defaults to [`LogLevel::Ignore`].
    pub ambiguity_detection: LogLevel,
    /// Determines whether the presence of redundant edges in the hierarchy of system sets is only
    /// logged or also results in a [`HierarchyRedundancy`](ScheduleBuildError::HierarchyRedundancy)
    /// error.
    ///
    /// Defaults to [`LogLevel::Warn`].
    pub hierarchy_detection: LogLevel,
    /// Auto insert [`ApplyDeferred`] systems into the schedule,
    /// when there are [`Deferred`](crate::prelude::Deferred)
    /// in one system and there are ordering dependencies on that system. [`Commands`](crate::system::Commands) is one
    /// such deferred buffer.
    ///
    /// You may want to disable this if you only want to sync deferred params at the end of the schedule,
    /// or want to manually insert all your sync points.
    ///
    /// Defaults to `true`
    pub auto_insert_apply_deferred: bool,
    /// If set to true, node names will be shortened instead of the fully qualified type path.
    ///
    /// Defaults to `true`.
    pub use_shortnames: bool,
    /// If set to true, report all system sets the conflicting systems are part of.
    ///
    /// Defaults to `true`.
    pub report_sets: bool,
}

impl Default for DefaultBuildSettings {
    fn default() -> Self {
        Self::new()
    }
}

impl DefaultBuildSettings {
    /// Default build settings.
    /// See the field-level documentation for the default value of each field.
    pub const fn new() -> Self {
        Self {
            ambiguity_detection: LogLevel::Ignore,
            hierarchy_detection: LogLevel::Warn,
            auto_insert_apply_deferred: true,
            use_shortnames: true,
            report_sets: true,
        }
    }
}

/// Specifies how schedule construction should respond to detecting a certain kind of issue.
#[derive(Debug, Clone, PartialEq)]
pub enum LogLevel {
    /// Occurrences are completely ignored.
    Ignore,
    /// Occurrences are logged only.
    Warn,
    /// Occurrences are logged and result in errors.
    Error,
}

/// Category of errors encountered during schedule construction.
#[derive(Error, Debug)]
#[non_exhaustive]
pub enum DefaultBuildError {
    /// A system set contains itself.
    #[error("System set `{0}` contains itself.")]
    HierarchyLoop(String),
    /// The hierarchy of system sets contains a cycle.
    #[error("System set hierarchy contains cycle(s).\n{0}")]
    HierarchyCycle(String),
    /// The hierarchy of system sets contains redundant edges.
    ///
    /// This error is disabled by default, but can be opted-in using [`ScheduleBuildSettings`].
    #[error("System set hierarchy contains redundant edges.\n{0}")]
    HierarchyRedundancy(String),
    /// A system (set) has been told to run before itself.
    #[error("System set `{0}` depends on itself.")]
    DependencyLoop(String),
    /// The dependency graph contains a cycle.
    #[error("System dependencies contain cycle(s).\n{0}")]
    DependencyCycle(String),
    /// Tried to order a system (set) relative to a system set it belongs to.
    #[error("`{0}` and `{1}` have both `in_set` and `before`-`after` relationships (these might be transitive). This combination is unsolvable as a system cannot run before or after a set it belongs to.")]
    CrossDependency(String, String),
    /// Tried to order system sets that share systems.
    #[error("`{0}` and `{1}` have a `before`-`after` relationship (which may be transitive) but share systems.")]
    SetsHaveOrderButIntersect(String, String),
    /// Tried to order a system (set) relative to all instances of some system function.
    #[error("Tried to order against `{0}` in a schedule that has more than one `{0}` instance. `{0}` is a `SystemTypeSet` and cannot be used for ordering if ambiguous. Use a different set without this restriction.")]
    SystemTypeSetAmbiguity(String),
    /// Systems with conflicting access have indeterminate run order.
    ///
    /// This error is disabled by default, but can be opted-in using [`ScheduleBuildSettings`].
    #[error("Systems with conflicting access have indeterminate run order.\n{0}")]
    Ambiguity(String),
    /// Tried to run a schedule before all of its systems have been initialized.
    #[error("Systems in schedule have not been initialized.")]
    Uninitialized,
}

/// Global metadata for [`DefaultGraph`] schedules that tracks ignored scheduling ambiguities.
#[derive(Deref, DerefMut, Clone, Default)]
pub struct IgnoredSchedulingAmbiguities(pub BTreeSet<ComponentId>);
