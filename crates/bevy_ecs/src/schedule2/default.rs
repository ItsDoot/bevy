use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::{
    any::{Any, TypeId},
    fmt::Write as _,
    hash::Hash,
};

use bevy_platform_support::collections::{HashMap, HashSet};
use bevy_utils::TypeIdMap;
use derive_more::derive::{Deref, DerefMut};
use disqualified::ShortName;
use fixedbitset::FixedBitSet;
use log::{error, warn};

use crate::{
    component::{ComponentId, Components, Tick},
    prelude::Condition,
    query::AccessConflicts,
    result::Result,
    schedule::{is_apply_deferred, BoxedCondition, LogLevel, ScheduleBuildError},
    schedule2::{
        graph::{
            check_graph, index, simple_cycles_in_component, Ambiguity, CheckGraphResults, Dag,
            Dependency, DependencyKind, DiGraph, Direction::*, UnGraph,
        },
        traits::ProcessedConfigs,
        AnonymousSet, DynScheduleBuildPass, GraphNode, GraphNodeId, IgnoreDeferred,
        IgnoredSchedulingAmbiguities, InternedScheduleLabel, InternedSystemSet, IntoNodeConfigs,
        IntoSystemSet, NodeConfig, NodeConfigs, Schedule, ScheduleBuildPass, ScheduleExecutable,
        ScheduleExecutor, ScheduleGraph, SimpleExecutor, SystemSet,
    },
    storage::SparseSetIndex,
    system::{BoxedSystem, InfallibleSystemWrapper, IntoSystem, System},
    world::World,
};

impl Schedule {
    /// Add a collection of systems to the schedule.
    pub fn add_systems<M>(
        &mut self,
        systems: impl IntoNodeConfigs<ScheduleSystem, M>,
    ) -> &mut Self {
        self.process_configs(systems)
    }

    /// Configures a collection of system sets in this schedule, adding them if they does not exist.
    #[track_caller]
    pub fn configure_sets<M>(
        &mut self,
        sets: impl IntoNodeConfigs<ScheduleSystemSet, M>,
    ) -> &mut Self {
        self.process_configs(sets)
    }
}

/// Metadata for a [`Schedule`].
///
/// The order isn't optimized; calling [`ScheduleGraph::build`] will return a
/// [`SystemGraphExecutable`] where the order is optimized for execution.
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
    system_set_ids: HashMap<InternedSystemSet, NodeId>,
    /// Systems that have not been initialized yet; for system sets, we store the index of the first uninitialized condition
    /// (all the conditions after that index still need to be initialized)
    uninit: Vec<(NodeId, usize)>,
    /// Directed acyclic graph of the hierarchy (which systems/sets are children of which sets)
    hierarchy: Dag<NodeId>,
    /// Directed acyclic graph of the dependency (which systems/sets have to run before which other systems/sets)
    dependency: Dag<NodeId>,
    ambiguous_with: UnGraph<NodeId>,
    /// Nodes that are allowed to have ambiguous ordering relationship with any other systems.
    pub ambiguous_with_all: HashSet<NodeId>,
    conflicting_systems: Vec<(NodeId, NodeId, Vec<ComponentId>)>,
    anonymous_sets: usize,
    changed: bool,
    settings: ScheduleBuildSettings,
    passes: BTreeMap<TypeId, Box<dyn DynScheduleBuildPass<Self>>>,
}

impl DefaultGraph {
    fn create_anonymous_set(&mut self) -> AnonymousSet {
        let id = self.anonymous_sets;
        self.anonymous_sets += 1;
        AnonymousSet::new(id)
    }

    fn add_system_inner(
        &mut self,
        config: NodeConfig<ScheduleSystem>,
    ) -> Result<NodeId, ScheduleBuildError> {
        let id = NodeId::System(self.systems.len());

        self.update_graphs(id, config.metadata.graph_info)?;

        self.uninit.push((id, 0));
        self.systems.push(SystemNode::new(config.node.0));
        self.system_conditions.push(config.metadata.conditions.0);

        Ok(id)
    }

    fn configure_set_inner(
        &mut self,
        mut config: NodeConfig<ScheduleSystemSet>,
    ) -> Result<NodeId, ScheduleBuildError> {
        let id = match self.system_set_ids.get(&config.node.0) {
            Some(&id) => id,
            None => self.add_set(config.node.0),
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

    fn apply_collective_conditions<T>(
        &mut self,
        configs: &mut [NodeConfigs<T>],
        collective_conditions: Vec<BoxedCondition>,
    ) where
        T: GraphNode<
            Metadata = NodeMetadata,
            GroupMetadata = NodeGroupMetadata,
            Graph = DefaultGraph,
        >,
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
                let mut set_config = ScheduleSystemSet(set.intern()).into_config();
                set_config.metadata.conditions.extend(collective_conditions);
                self.configure_set_inner(set_config).unwrap();
            }
        }
    }

    fn update_graphs(
        &mut self,
        id: NodeId,
        graph_info: GraphInfo,
    ) -> Result<(), ScheduleBuildError> {
        self.check_hierarchy_sets(&id, &graph_info)?;
        self.check_edges(&id, &graph_info)?;
        self.changed = true;

        let GraphInfo {
            hierarchy: sets,
            dependencies,
            ambiguous_with,
            ..
        } = graph_info;

        self.hierarchy.graph.add_node(id);
        self.dependency.graph.add_node(id);

        for set in sets.into_iter().map(|set| self.system_set_ids[&set]) {
            self.hierarchy.graph.add_edge(set, id);

            // ensure set also appears in dependency graph
            self.dependency.graph.add_node(set);
        }

        for (kind, set, options) in dependencies
            .into_iter()
            .map(|Dependency { kind, set, options }| (kind, self.system_set_ids[&set], options))
        {
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
            Ambiguity::Check => (),
            Ambiguity::IgnoreWithSet(ambiguous_with) => {
                for set in ambiguous_with
                    .into_iter()
                    .map(|set| self.system_set_ids[&set])
                {
                    self.ambiguous_with.add_edge(id, set);
                }
            }
            Ambiguity::IgnoreAll => {
                self.ambiguous_with_all.insert(id);
            }
        }

        Ok(())
    }

    /// Check that no set is included in itself.
    /// Add all the sets from the [`GraphInfo`]'s hierarchy to the graph.
    fn check_hierarchy_sets(
        &mut self,
        id: &NodeId,
        graph_info: &GraphInfo,
    ) -> Result<(), ScheduleBuildError> {
        for &set in &graph_info.hierarchy {
            self.check_hierarchy_set(id, set)?;
        }

        Ok(())
    }

    /// Checks that a system set isn't included in itself.
    /// If not present, add the set to the graph.
    fn check_hierarchy_set(
        &mut self,
        id: &NodeId,
        set: InternedSystemSet,
    ) -> Result<(), ScheduleBuildError> {
        match self.system_set_ids.get(&set) {
            Some(set_id) => {
                if id == set_id {
                    return Err(ScheduleBuildError::HierarchyLoop(self.get_node_name(id)));
                }
            }
            None => {
                self.add_set(set);
            }
        }

        Ok(())
    }

    /// Checks that no system set is dependent on itself.
    /// Add all the sets from the [`GraphInfo`]'s dependencies to the graph.
    fn check_edges(
        &mut self,
        id: &NodeId,
        graph_info: &GraphInfo,
    ) -> Result<(), ScheduleBuildError> {
        for Dependency { set, .. } in &graph_info.dependencies {
            match self.system_set_ids.get(set) {
                Some(set_id) => {
                    if id == set_id {
                        return Err(ScheduleBuildError::DependencyLoop(self.get_node_name(id)));
                    }
                }
                None => {
                    self.add_set(*set);
                }
            }
        }

        if let Ambiguity::IgnoreWithSet(ambiguous_with) = &graph_info.ambiguous_with {
            for set in ambiguous_with {
                if !self.system_set_ids.contains_key(set) {
                    self.add_set(*set);
                }
            }
        }

        Ok(())
    }

    /// Common implementation between [`System`] and [`SystemSet`] node configs.
    fn process_configs<N>(
        &mut self,
        configs: NodeConfigs<N>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<N>, ScheduleBuildError>
    where
        N: GraphNode<
            Metadata = NodeMetadata,
            GroupMetadata = NodeGroupMetadata,
            ProcessData = DenselyChained,
            Graph = Self,
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

                let is_chained = metadata.chain.is_chained();

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
                    Self::process_configs(self, first, collect_nodes || is_chained)?;
                densely_chained &= previous_result.data.0;

                for current in configs {
                    let current_result =
                        Self::process_configs(self, current, collect_nodes || is_chained)?;
                    densely_chained &= current_result.data.0;

                    if let Chain::Chained(chain_options) = &metadata.chain {
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
}

/// Used to select the appropriate reporting function.
pub enum ReportCycles {
    /// When sets contain themselves
    Hierarchy,
    /// When the graph is no longer a DAG
    Dependency,
}

// methods for reporting errors
impl DefaultGraph {
    fn get_node_name(&self, id: &NodeId) -> String {
        self.get_node_name_inner(id, self.settings.report_sets)
    }

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

    fn get_node_kind(&self, id: &NodeId) -> &'static str {
        match id {
            NodeId::System(_) => "system",
            NodeId::Set(_) => "system set",
        }
    }

    /// If [`ScheduleBuildSettings::hierarchy_detection`] is [`LogLevel::Ignore`] this check
    /// is skipped.
    fn optionally_check_hierarchy_conflicts(
        &self,
        transitive_edges: &[(NodeId, NodeId)],
        schedule_label: InternedScheduleLabel,
    ) -> Result<(), ScheduleBuildError> {
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
            LogLevel::Error => Err(ScheduleBuildError::HierarchyRedundancy(message)),
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
                self.get_node_kind(child),
                self.get_node_name(child),
                self.get_node_name(parent),
            )
            .unwrap();
        }

        message
    }

    /// Tries to topologically sort `graph`.
    ///
    /// If the graph is acyclic, returns [`Ok`] with the list of [`NodeId`] in a valid
    /// topological order. If the graph contains cycles, returns [`Err`] with the list of
    /// strongly-connected components that contain cycles (also in a valid topological order).
    ///
    /// # Errors
    ///
    /// If the graph contain cycles, then an error is returned.
    pub fn topsort_graph(
        &self,
        graph: &DiGraph<NodeId>,
        report: ReportCycles,
    ) -> Result<Vec<NodeId>, ScheduleBuildError> {
        // Tarjan's SCC algorithm returns elements in *reverse* topological order.
        let mut top_sorted_nodes = Vec::with_capacity(graph.node_count());
        let mut sccs_with_cycles = Vec::new();

        for scc in graph.iter_sccs() {
            // A strongly-connected component is a group of nodes who can all reach each other
            // through one or more paths. If an SCC contains more than one node, there must be
            // at least one cycle within them.
            top_sorted_nodes.extend_from_slice(&scc);
            if scc.len() > 1 {
                sccs_with_cycles.push(scc);
            }
        }

        if sccs_with_cycles.is_empty() {
            // reverse to get topological order
            top_sorted_nodes.reverse();
            Ok(top_sorted_nodes)
        } else {
            let mut cycles = Vec::new();
            for scc in &sccs_with_cycles {
                cycles.append(&mut simple_cycles_in_component(graph, scc));
            }

            let error = match report {
                ReportCycles::Hierarchy => ScheduleBuildError::HierarchyCycle(
                    self.get_hierarchy_cycles_error_message(&cycles),
                ),
                ReportCycles::Dependency => ScheduleBuildError::DependencyCycle(
                    self.get_dependency_cycles_error_message(&cycles),
                ),
            };

            Err(error)
        }
    }

    /// Logs details of cycles in the hierarchy graph.
    fn get_hierarchy_cycles_error_message(&self, cycles: &[Vec<NodeId>]) -> String {
        let mut message = format!("schedule has {} in_set cycle(s):\n", cycles.len());
        for (i, cycle) in cycles.iter().enumerate() {
            let mut names = cycle.iter().map(|id| self.get_node_name(id));
            let first_name = names.next().unwrap();
            writeln!(
                message,
                "cycle {}: set `{first_name}` contains itself",
                i + 1,
            )
            .unwrap();
            writeln!(message, "set `{first_name}`").unwrap();
            for name in names.chain(core::iter::once(first_name)) {
                writeln!(message, " ... which contains set `{name}`").unwrap();
            }
            writeln!(message).unwrap();
        }

        message
    }

    /// Logs details of cycles in the dependency graph.
    fn get_dependency_cycles_error_message(&self, cycles: &[Vec<NodeId>]) -> String {
        let mut message = format!("schedule has {} before/after cycle(s):\n", cycles.len());
        for (i, cycle) in cycles.iter().enumerate() {
            let mut names = cycle
                .iter()
                .map(|id| (self.get_node_kind(id), self.get_node_name(id)));
            let (first_kind, first_name) = names.next().unwrap();
            writeln!(
                message,
                "cycle {}: {first_kind} `{first_name}` must run before itself",
                i + 1,
            )
            .unwrap();
            writeln!(message, "{first_kind} `{first_name}`").unwrap();
            for (kind, name) in names.chain(core::iter::once((first_kind, first_name))) {
                writeln!(message, " ... which must run before {kind} `{name}`").unwrap();
            }
            writeln!(message).unwrap();
        }

        message
    }

    fn check_for_cross_dependencies(
        &self,
        dep_results: &CheckGraphResults<NodeId>,
        hier_results_connected: &HashSet<(NodeId, NodeId)>,
    ) -> Result<(), ScheduleBuildError> {
        for &(a, b) in &dep_results.connected {
            if hier_results_connected.contains(&(a, b)) || hier_results_connected.contains(&(b, a))
            {
                let name_a = self.get_node_name(&a);
                let name_b = self.get_node_name(&b);
                return Err(ScheduleBuildError::CrossDependency(name_a, name_b));
            }
        }

        Ok(())
    }

    fn check_order_but_intersect(
        &self,
        dep_results_connected: &HashSet<(NodeId, NodeId)>,
        set_system_bitsets: &HashMap<NodeId, FixedBitSet>,
    ) -> Result<(), ScheduleBuildError> {
        // check that there is no ordering between system sets that intersect
        for (a, b) in dep_results_connected {
            if !(a.is_set() && b.is_set()) {
                continue;
            }

            let a_systems = set_system_bitsets.get(a).unwrap();
            let b_systems = set_system_bitsets.get(b).unwrap();

            if !a_systems.is_disjoint(b_systems) {
                return Err(ScheduleBuildError::SetsHaveOrderButIntersect(
                    self.get_node_name(a),
                    self.get_node_name(b),
                ));
            }
        }

        Ok(())
    }

    fn check_system_type_set_ambiguity(
        &self,
        set_systems: &HashMap<NodeId, Vec<NodeId>>,
    ) -> Result<(), ScheduleBuildError> {
        for (&id, systems) in set_systems {
            let set = &self.system_sets[id.index()];
            if set.is_system_type() {
                let instances = systems.len();
                let ambiguous_with = self.ambiguous_with.edges(id);
                let before = self.dependency.graph.edges_directed(id, Incoming);
                let after = self.dependency.graph.edges_directed(id, Outgoing);
                let relations = before.count() + after.count() + ambiguous_with.count();
                if instances > 1 && relations > 0 {
                    return Err(ScheduleBuildError::SystemTypeSetAmbiguity(
                        self.get_node_name(&id),
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
    ) -> Result<(), ScheduleBuildError> {
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
            LogLevel::Error => Err(ScheduleBuildError::Ambiguity(message)),
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
            .map(move |(system_a, system_b, conflicts)| {
                let name_a = self.get_node_name(system_a);
                let name_b = self.get_node_name(system_b);

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
            .map(|set_id| self.get_node_name(&set_id))
            .collect();
        sets.sort();
        sets
    }

    /// Build a [`DefaultGraphExecutable`] optimized for scheduler access from the [`ScheduleGraph`].
    ///
    /// This method also
    /// - checks for dependency or hierarchy cycles
    /// - checks for system access conflicts and reports ambiguities
    pub fn build_schedule(
        &mut self,
        world: &mut World,
        schedule_label: InternedScheduleLabel,
        ignored_ambiguities: &BTreeSet<ComponentId>,
    ) -> Result<DefaultGraphExecutable, ScheduleBuildError> {
        // check hierarchy for cycles
        self.hierarchy.topsort =
            self.topsort_graph(&self.hierarchy.graph, ReportCycles::Hierarchy)?;

        let hier_results = check_graph(&self.hierarchy.graph, &self.hierarchy.topsort);
        self.optionally_check_hierarchy_conflicts(&hier_results.transitive_edges, schedule_label)?;

        // remove redundant edges
        self.hierarchy.graph = hier_results.transitive_reduction;

        // check dependencies for cycles
        self.dependency.topsort =
            self.topsort_graph(&self.dependency.graph, ReportCycles::Dependency)?;

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
            topsort: self.topsort_graph(&dependency_flattened, ReportCycles::Dependency)?,
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

impl ScheduleGraph for DefaultGraph {
    type Id = NodeId;
    type Executable = DefaultGraphExecutable;
    type BuildError = ScheduleBuildError;
    type BuildSettings = ScheduleBuildSettings;
    type ExecutorKind = ExecutorKind;
    type GlobalMetadata = IgnoredSchedulingAmbiguities;

    fn new_executor(kind: Self::ExecutorKind) -> Box<dyn ScheduleExecutor<Self>> {
        match kind {
            ExecutorKind::Simple => Box::new(SimpleExecutor::new()),
            // ExecutorKind::SingleThreaded => Box::new(SingleThreadedExecutor::new()),
            // #[cfg(feature = "std")]
            // ExecutorKind::MultiThreaded => Box::new(MultiThreadedExecutor::new()),
            _ => todo!(),
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
        self.settings = settings;
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
            return Err(ScheduleBuildError::Uninitialized);
        }

        // move systems out of old schedule
        for ((id, system), conditions) in executable
            .system_ids
            .drain(..)
            .zip(executable.systems.drain(..))
            .zip(executable.system_conditions.drain(..))
        {
            self.systems[id.index()].inner = Some(system.0);
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
            executable.systems.push(ScheduleSystem(system));
            executable.system_conditions.push(conditions);
        }

        for &id in &executable.set_ids {
            let conditions = core::mem::take(&mut self.system_set_conditions[id.index()]);
            executable.set_conditions.push(conditions);
        }

        Ok(())
    }
}

/// A [`SystemSet`] with metadata, stored in a [`ScheduleGraph`].
pub(crate) struct SystemSetNode {
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

/// A [`ScheduleSystem`] stored in a [`ScheduleGraph`].
pub struct SystemNode {
    inner: Option<BoxedSystem<(), Result>>,
}

impl SystemNode {
    /// Create a new [`SystemNode`]
    pub fn new(system: BoxedSystem<(), Result>) -> Self {
        Self {
            inner: Some(system),
        }
    }

    /// Obtain a reference to the [`ScheduleSystem`] represented by this node.
    pub fn get(&self) -> Option<&BoxedSystem<(), Result>> {
        self.inner.as_ref()
    }

    /// Obtain a mutable reference to the [`ScheduleSystem`] represented by this node.
    pub fn get_mut(&mut self) -> Option<&mut BoxedSystem<(), Result>> {
        self.inner.as_mut()
    }
}

/// Holds systems and conditions of a [`Schedule`](super::Schedule) sorted in topological order
/// (along with dependency information for `multi_threaded` execution).
///referenced by their index.
/// [`FixedBitSet`] is used as a smaller, more efficient substitute
/// Since the arrays are sorted in the same order, elements are  of `HashSet<usize>`.
#[derive(Default)]
pub struct DefaultGraphExecutable {
    /// List of system node ids.
    pub(super) system_ids: Vec<NodeId>,
    /// Indexed by system node id.
    pub(super) systems: Vec<ScheduleSystem>,
    /// Indexed by system node id.
    pub(super) system_conditions: Vec<Vec<BoxedCondition>>,
    /// Indexed by system node id.
    /// Number of systems that the system immediately depends on.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(super) system_dependencies: Vec<usize>,
    /// Indexed by system node id.
    /// List of systems that immediately depend on the system.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(super) system_dependents: Vec<Vec<usize>>,
    /// Indexed by system node id.
    /// List of sets containing the system that have conditions
    pub(super) sets_with_conditions_of_systems: Vec<FixedBitSet>,
    /// List of system set node ids.
    pub(super) set_ids: Vec<NodeId>,
    /// Indexed by system set node id.
    pub(super) set_conditions: Vec<Vec<BoxedCondition>>,
    /// Indexed by system set node id.
    /// List of systems that are in sets that have conditions.
    ///
    /// If a set doesn't run because of its conditions, this is used to skip all systems in it.
    pub(super) systems_in_sets_with_conditions: Vec<FixedBitSet>,
}

impl ScheduleExecutable for DefaultGraphExecutable {
    fn apply_deferred(&mut self, world: &mut World) {
        for system in &mut self.systems {
            system.0.apply_deferred(world);
        }
    }

    fn check_change_ticks(&mut self, change_tick: Tick) {
        for system in &mut self.systems {
            if !is_apply_deferred(&system.0) {
                system.0.check_change_tick(change_tick);
            }
        }
        for conditions in &mut self.system_conditions {
            for condition in conditions {
                condition.check_change_tick(change_tick);
            }
        }
        for conditions in &mut self.set_conditions {
            for condition in conditions {
                condition.check_change_tick(change_tick);
            }
        }
    }
}

/// Unique identifier for a system or system set stored in a [`SystemGraph`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum NodeId {
    /// Identifier for a system.
    System(usize),
    /// Identifier for a system set.
    Set(usize),
}

impl NodeId {
    /// Returns `true` if this identifier refers to a system.
    pub fn is_system(&self) -> bool {
        matches!(self, NodeId::System(_))
    }

    /// Returns `true` if this identifier refers to a system set.
    pub fn is_set(&self) -> bool {
        matches!(self, NodeId::Set(_))
    }
}

impl GraphNodeId for NodeId {
    fn index(&self) -> usize {
        match *self {
            NodeId::System(index) | NodeId::Set(index) => index,
        }
    }
}

/// Specifies miscellaneous settings for schedule construction.
#[derive(Clone, Debug)]
pub struct ScheduleBuildSettings {
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

impl Default for ScheduleBuildSettings {
    fn default() -> Self {
        Self::new()
    }
}

impl ScheduleBuildSettings {
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

/// A [`GraphNode`] in a [`SystemGraph`] that represents a system.
#[repr(transparent)]
pub struct ScheduleSystem(pub(crate) BoxedSystem<(), Result>);

impl GraphNode for ScheduleSystem {
    type Metadata = NodeMetadata;
    type GroupMetadata = NodeGroupMetadata;
    type ProcessData = DenselyChained;
    type Graph = DefaultGraph;

    fn into_config(self) -> NodeConfig<Self> {
        let sets = self.0.default_system_sets().clone();
        NodeConfig {
            node: self,
            metadata: NodeMetadata {
                graph_info: GraphInfo {
                    hierarchy: sets,
                    ..GraphInfo::default()
                },
                conditions: Conditions::default(),
            },
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self>,
    ) -> Result<NodeId, ScheduleBuildError> {
        graph.add_system_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self>, ScheduleBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// A [`GraphNode`] in a [`SystemGraph`] that represents a system set.
#[repr(transparent)]
pub struct ScheduleSystemSet(InternedSystemSet);

impl GraphNode for ScheduleSystemSet {
    type Metadata = NodeMetadata;
    type GroupMetadata = NodeGroupMetadata;
    type ProcessData = DenselyChained;
    type Graph = DefaultGraph;

    fn into_config(self) -> NodeConfig<Self> {
        // system type sets are automatically populated
        // to avoid unintentionally broad changes, they cannot be configured
        assert!(
            self.0.system_type().is_none(),
            "configuring system type sets is not allowed"
        );

        NodeConfig {
            node: self,
            metadata: NodeMetadata::default(),
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self>,
    ) -> Result<NodeId, ScheduleBuildError> {
        graph.configure_set_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self>, ScheduleBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// Stores whether a group of nodes are densely chained.
pub struct DenselyChained(bool);

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

/// Metadata for [`ScheduleSystem`] and [`ScheduleSystemSet`] nodes.
#[derive(Default)]
pub struct NodeMetadata {
    /// Hierarchy and dependency metadata for this node.
    pub graph_info: GraphInfo,
    /// Conditions for this node to be able to run.
    pub conditions: Conditions,
}

impl AsMut<GraphInfo> for NodeMetadata {
    fn as_mut(&mut self) -> &mut GraphInfo {
        &mut self.graph_info
    }
}

impl AsMut<Conditions> for NodeMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.conditions
    }
}

/// Metadata for groups of [`ScheduleSystem`] and [`ScheduleSystemSet`] nodes.
#[derive(Default)]
pub struct NodeGroupMetadata {
    /// Ordering metadata for this group of nodes.
    pub chain: Chain,
    /// Conditions for this group of nodes to be able to run.
    pub collective_conditions: Conditions,
}

impl AsMut<Chain> for NodeGroupMetadata {
    fn as_mut(&mut self) -> &mut Chain {
        &mut self.chain
    }
}

impl AsMut<Conditions> for NodeGroupMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.collective_conditions
    }
}

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

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Infallible;

impl<F, Marker> IntoNodeConfigs<ScheduleSystem, (Infallible, Marker)> for F
where
    F: IntoSystem<(), (), Marker>,
{
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        let wrapper = InfallibleSystemWrapper::new(IntoSystem::into_system(self));
        NodeConfigs::Single(ScheduleSystem(Box::new(wrapper)).into_config())
    }
}

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Fallible;

impl<F, Marker> IntoNodeConfigs<ScheduleSystem, (Fallible, Marker)> for F
where
    F: IntoSystem<(), Result, Marker>,
{
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        let boxed_system = Box::new(IntoSystem::into_system(self));
        NodeConfigs::Single(ScheduleSystem(boxed_system).into_config())
    }
}

impl IntoNodeConfigs<ScheduleSystem, ()> for BoxedSystem<(), Result> {
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        NodeConfigs::Single(ScheduleSystem(self).into_config())
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

/// Specifies how a [`SystemGraph`] [`Schedule`](super::Schedule) will be run.
///
/// The default depends on the target platform:
///  - [`SingleThreaded`](ExecutorKind::SingleThreaded) on Wasm.
///  - [`MultiThreaded`](ExecutorKind::MultiThreaded) everywhere else.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum ExecutorKind {
    /// Runs the schedule using a single thread.
    ///
    /// Useful if you're dealing with a single-threaded environment, saving your threads for
    /// other things, or just trying minimize overhead.
    #[cfg_attr(any(target_arch = "wasm32", not(feature = "multi_threaded")), default)]
    SingleThreaded,
    /// Like [`SingleThreaded`](ExecutorKind::SingleThreaded) but calls [`apply_deferred`](crate::system::System::apply_deferred)
    /// immediately after running each system.
    Simple,
    /// Runs the schedule using a thread pool. Non-conflicting systems can run in parallel.
    #[cfg(feature = "std")]
    #[cfg_attr(all(not(target_arch = "wasm32"), feature = "multi_threaded"), default)]
    MultiThreaded,
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
