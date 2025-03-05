use alloc::collections::BTreeMap;
use core::{any::TypeId, fmt::Write as _, marker::PhantomData};
use disqualified::ShortName;
use fixedbitset::FixedBitSet;

use bevy_ecs::{
    component::Tick,
    result::Result,
    schedule::{
        default::{DenselyChained, LogLevel},
        graph::{
            check_graph, simple_cycles_in_component, CheckGraphResults, Dag, DiGraph, Direction,
        },
        traits::{GraphNode, ProcessedConfigs, ScheduleExecutable, ScheduleGraph},
        Chain, Dependencies, Dependency, DependencyKind, Hierarchy, InternedScheduleLabel,
        InternedSystemSet, NodeConfigs, ReportCycles, ScheduleBuildPass, ScheduleBuildPassObj,
        ScheduleExecutor,
    },
    system::{BoxedReadOnlySystem, SystemInput},
    world::World,
};
use bevy_platform_support::collections::{HashMap, HashSet};
use wgpu::CommandBuffer;

use crate::render_graph2::{node::RenderNodeId, RenderGroupMetadata, RenderNodeMetadata};

/// Metadata for a [`Schedule`].
///
/// The order isn't optimized; calling `ScheduleGraph::build_schedule` will return a
/// `SystemSchedule` where the order is optimized for execution.
#[derive(Default)]
pub struct RenderGraph {
    /// List of systems in the schedule
    pub systems: Vec<RenderNode>,
    /// List of system sets in the schedule
    system_sets: Vec<InternedSystemSet>,
    /// Map from system set to node id
    pub(crate) system_set_ids: HashMap<InternedSystemSet, RenderNodeId>,
    /// Systems that have not been initialized yet.
    pub(super) uninit: Vec<usize>,
    /// Directed acyclic graph of the hierarchy (which systems/sets are children of which sets)
    hierarchy: Dag<RenderNodeId>,
    /// Directed acyclic graph of the dependency (which systems/sets have to run before which other systems/sets)
    dependency: Dag<RenderNodeId>,
    settings: RenderGraphBuildSettings,
    changed: bool,
    passes: BTreeMap<TypeId, Box<dyn ScheduleBuildPassObj<Self>>>,
}

impl RenderGraph {
    pub(super) fn update_graphs(
        &mut self,
        id: RenderNodeId,
        hierarchy: Hierarchy<InternedSystemSet>,
        dependencies: Dependencies<InternedSystemSet>,
    ) -> Result<(), RenderGraphError> {
        self.try_add_hierarchy_sets(id, &hierarchy)?;
        self.try_add_dependency_sets(id, &dependencies)?;
        self.changed = true;

        self.hierarchy.graph.add_node(id);
        self.dependency.graph.add_node(id);

        for set in hierarchy.0.into_iter().map(|set| self.system_set_ids[&set]) {
            self.hierarchy.graph.add_edge(set, id);
            // Ensure set also appears in the dependency graph
            self.dependency.graph.add_node(set);
        }

        for (kind, set, options) in dependencies
            .0
            .into_iter()
            .map(|dep| (dep.kind, self.system_set_ids[&dep.target], dep.options))
        {
            let (lhs, rhs) = match kind {
                DependencyKind::Before => (id, set),
                DependencyKind::After => (set, id),
            };
            self.dependency.graph.add_edge(lhs, rhs);
            for pass in self.passes.values_mut() {
                pass.add_dependency(lhs, rhs, &options);
            }

            // Ensure set also appears in the hierarchy graph
            self.hierarchy.graph.add_node(set);
        }

        Ok(())
    }

    /// Adds all sets in the hierarchy while ensuring no set is included in itself.
    fn try_add_hierarchy_sets(
        &mut self,
        id: RenderNodeId,
        hierarchy: &Hierarchy<InternedSystemSet>,
    ) -> Result<(), RenderGraphError> {
        for set in &hierarchy.0 {
            match self.system_set_ids.get(set) {
                Some(set_id) => {
                    if id == *set_id {
                        return Err(RenderGraphError::HierarchyLoop(self.get_node_name(id)));
                    }
                }
                None => {
                    self.add_set(*set);
                }
            }
        }

        Ok(())
    }

    /// Adds all sets in the dependencies while ensuring no set is dependent on itself.
    fn try_add_dependency_sets(
        &mut self,
        id: RenderNodeId,
        dependencies: &Dependencies<InternedSystemSet>,
    ) -> Result<(), RenderGraphError> {
        for Dependency { target: set, .. } in &dependencies.0 {
            match self.system_set_ids.get(set) {
                Some(set_id) => {
                    if id == *set_id {
                        return Err(RenderGraphError::DependencyLoop(self.get_node_name(id)));
                    }
                }
                None => {
                    self.add_set(*set);
                }
            }
        }

        Ok(())
    }

    /// Tries to topologically sort `graph`.
    ///
    /// If the graph is acyclic, returns [`Ok`] with the list of [`RenderNodeId`] in a valid
    /// topological order. If the graph contains cycles, returns [`Err`] with the list of
    /// strongly-connected components that contain cycles (also in a valid topological order).
    ///
    /// # Errors
    ///
    /// If the graph contain cycles, then an error is returned.
    fn topsort_graph(
        &self,
        graph: &DiGraph<RenderNodeId>,
        report: ReportCycles,
    ) -> Result<Vec<RenderNodeId>, RenderGraphError> {
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
                ReportCycles::Hierarchy => RenderGraphError::HierarchyCycle(
                    self.get_hierarchy_cycles_error_message(&cycles),
                ),
                ReportCycles::Dependency => RenderGraphError::DependencyCycle(
                    self.get_dependency_cycles_error_message(&cycles),
                ),
            };

            Err(error)
        }
    }

    /// Logs details of cycles in the hierarchy graph.
    fn get_hierarchy_cycles_error_message(&self, cycles: &[Vec<RenderNodeId>]) -> String {
        let mut message = format!("schedule has {} in_set cycle(s):\n", cycles.len());
        for (i, cycle) in cycles.iter().enumerate() {
            let mut names = cycle.iter().map(|&id| self.get_node_name(id));
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
    fn get_dependency_cycles_error_message(&self, cycles: &[Vec<RenderNodeId>]) -> String {
        let mut message = format!("schedule has {} before/after cycle(s):\n", cycles.len());
        for (i, cycle) in cycles.iter().enumerate() {
            let mut names = cycle
                .iter()
                .map(|&id| (id.type_name(), self.get_node_name(id)));
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

    pub(super) fn process_configs<N>(
        &mut self,
        configs: NodeConfigs<N, Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<N, Self>, RenderGraphError>
    where
        N: GraphNode<
            Self,
            Metadata = RenderNodeMetadata,
            GroupMetadata = RenderGroupMetadata,
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
            NodeConfigs::Group { configs, metadata } => {
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

    pub(super) fn add_set(&mut self, set: InternedSystemSet) -> RenderNodeId {
        let id = RenderNodeId::Set(self.system_sets.len());
        self.system_sets.push(set);
        self.system_set_ids.insert(set, id);
        id
    }

    fn build_schedule(
        &mut self,
        world: &mut World,
        schedule_label: InternedScheduleLabel,
    ) -> Result<RenderGraphExecutable, RenderGraphError> {
        // Check hierarchy for cycles
        self.hierarchy.topsort =
            self.topsort_graph(&self.hierarchy.graph, ReportCycles::Hierarchy)?;

        let hier_results = check_graph(&self.hierarchy.graph, &self.hierarchy.topsort);
        self.optionally_check_hierarchy_conflicts(&hier_results.transitive_edges, schedule_label)?;

        // Remove redundant edges
        self.hierarchy.graph = hier_results.transitive_reduction;

        // Check dependencies for cycles
        self.dependency.topsort =
            self.topsort_graph(&self.dependency.graph, ReportCycles::Dependency)?;

        // Check for systems or system sets depending on sets they belong to
        let dep_results = check_graph(&self.dependency.graph, &self.dependency.topsort);
        self.check_for_cross_dependencies(&dep_results, &hier_results.connected)?;

        // Map all system sets to their systems; go in reverse topological order (bottom-up) for efficiency
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

        Ok(self.build_schedule_inner(dependency_flattened_dag))
    }

    /// Return a map from system set `RenderNodeId` to a list of system `RenderNodeId`s that are included in the set.
    /// Also return a map from system set `RenderNodeId` to a `FixedBitSet` of system `RenderNodeId`s that are included in the set,
    /// where the bitset order is the same as `self.systems`
    fn map_sets_to_systems(
        &self,
        hierarchy_topsort: &[RenderNodeId],
        hierarchy_graph: &DiGraph<RenderNodeId>,
    ) -> (
        HashMap<RenderNodeId, Vec<RenderNodeId>>,
        HashMap<RenderNodeId, FixedBitSet>,
    ) {
        let mut set_systems: HashMap<RenderNodeId, Vec<RenderNodeId>> =
            HashMap::with_capacity_and_hasher(self.system_sets.len(), Default::default());
        let mut set_system_bitsets =
            HashMap::with_capacity_and_hasher(self.system_sets.len(), Default::default());
        for &id in hierarchy_topsort.iter().rev() {
            if id.is_system() {
                continue;
            }

            let mut systems = Vec::new();
            let mut system_bitset = FixedBitSet::with_capacity(self.systems.len());

            for child in hierarchy_graph.neighbors_directed(id, Direction::Outgoing) {
                match child {
                    RenderNodeId::System(_) => {
                        systems.push(child);
                        system_bitset.insert(child.index());
                    }
                    RenderNodeId::Set(_) => {
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

    fn check_order_but_intersect(
        &self,
        dep_results_connected: &HashSet<(RenderNodeId, RenderNodeId)>,
        set_system_bitsets: &HashMap<RenderNodeId, FixedBitSet>,
    ) -> Result<(), RenderGraphError> {
        // check that there is no ordering between system sets that intersect
        for &(a, b) in dep_results_connected {
            if !(a.is_set() && b.is_set()) {
                continue;
            }

            let a_systems = set_system_bitsets.get(&a).unwrap();
            let b_systems = set_system_bitsets.get(&b).unwrap();

            if !a_systems.is_disjoint(b_systems) {
                return Err(RenderGraphError::SetsHaveOrderButIntersect(
                    self.get_node_name(a),
                    self.get_node_name(b),
                ));
            }
        }

        Ok(())
    }

    fn check_system_type_set_ambiguity(
        &self,
        set_systems: &HashMap<RenderNodeId, Vec<RenderNodeId>>,
    ) -> Result<(), RenderGraphError> {
        for (&id, systems) in set_systems {
            let set = &self.system_sets[id.index()];
            if set.system_type().is_some() {
                let instances = systems.len();
                let before = self
                    .dependency
                    .graph
                    .edges_directed(id, Direction::Incoming);
                let after = self
                    .dependency
                    .graph
                    .edges_directed(id, Direction::Outgoing);
                let relations = before.count() + after.count();
                if instances > 1 && relations > 0 {
                    return Err(RenderGraphError::SystemTypeSetAmbiguity(
                        self.get_node_name(id),
                    ));
                }
            }
        }
        Ok(())
    }

    fn get_dependency_flattened(
        &mut self,
        set_systems: &HashMap<RenderNodeId, Vec<RenderNodeId>>,
    ) -> DiGraph<RenderNodeId> {
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
                for a in dependency_flattened.neighbors_directed(set, Direction::Incoming) {
                    for b in dependency_flattened.neighbors_directed(set, Direction::Outgoing) {
                        temp.push((a, b));
                    }
                }
            } else {
                for a in dependency_flattened.neighbors_directed(set, Direction::Incoming) {
                    for &sys in systems {
                        temp.push((a, sys));
                    }
                }

                for b in dependency_flattened.neighbors_directed(set, Direction::Outgoing) {
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

    fn build_schedule_inner(
        &self,
        dependency_flattened_dag: Dag<RenderNodeId>,
    ) -> RenderGraphExecutable {
        let dg_system_ids = dependency_flattened_dag.topsort.clone();
        let sys_count = self.systems.len();

        RenderGraphExecutable {
            system_ids: dg_system_ids
                .into_iter()
                .map(|id| match id {
                    RenderNodeId::System(idx) => idx,
                    RenderNodeId::Set(_) => unreachable!("sets shouldn't have been included"),
                })
                .collect(),
            systems: Vec::with_capacity(sys_count),
        }
    }
}

/// Functions for reporting errors.
impl RenderGraph {
    fn get_node_name(&self, id: RenderNodeId) -> String {
        self.get_node_name_inner(id, self.settings.report_sets)
    }

    #[inline]
    fn get_node_name_inner(&self, id: RenderNodeId, report_sets: bool) -> String {
        let name = match id {
            RenderNodeId::System(_) => {
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
            RenderNodeId::Set(_) => {
                let set = &self.system_sets[id.index()];
                if set.is_anonymous() {
                    self.anonymous_set_name(id)
                } else {
                    format!("{:?}", set)
                }
            }
        };
        if self.settings.use_shortnames {
            ShortName(&name).to_string()
        } else {
            name
        }
    }

    fn anonymous_set_name(&self, id: RenderNodeId) -> String {
        format!(
            "({})",
            self.hierarchy
                .graph
                .edges_directed(id, Direction::Outgoing)
                // never get the sets of the members or this will infinite recurse when the report_sets setting is on.
                .map(|(_, member_id)| self.get_node_name_inner(member_id, false))
                .reduce(|a, b| format!("{a}, {b}"))
                .unwrap_or_default()
        )
    }

    fn names_of_sets_containing_node(&self, id: RenderNodeId) -> Vec<String> {
        let mut sets = <HashSet<_>>::default();
        self.traverse_sets_containing_node(id, &mut |set_id| {
            !self.system_sets[set_id.index()].system_type().is_some() && sets.insert(set_id)
        });
        let mut sets: Vec<_> = sets
            .into_iter()
            .map(|set_id| self.get_node_name(set_id))
            .collect();
        sets.sort();
        sets
    }

    fn traverse_sets_containing_node(
        &self,
        id: RenderNodeId,
        f: &mut impl FnMut(RenderNodeId) -> bool,
    ) {
        for (set_id, _) in self.hierarchy.graph.edges_directed(id, Direction::Incoming) {
            if f(set_id) {
                self.traverse_sets_containing_node(set_id, f);
            }
        }
    }

    /// If [`ScheduleBuildSettings::hierarchy_detection`] is [`LogLevel::Ignore`] this check
    /// is skipped.
    fn optionally_check_hierarchy_conflicts(
        &self,
        transitive_edges: &[(RenderNodeId, RenderNodeId)],
        schedule_label: InternedScheduleLabel,
    ) -> Result<(), RenderGraphError> {
        if self.settings.hierarchy_detection == LogLevel::Ignore || transitive_edges.is_empty() {
            return Ok(());
        }

        let message = self.get_hierarchy_conflicts_error_message(transitive_edges);
        match self.settings.hierarchy_detection {
            LogLevel::Ignore => unreachable!(),
            LogLevel::Warn => {
                log::error!(
                    "Schedule {schedule_label:?} has redundant edges:\n {}",
                    message
                );
                Ok(())
            }
            LogLevel::Error => Err(RenderGraphError::HierarchyRedundancy(message)),
        }
    }

    fn get_hierarchy_conflicts_error_message(
        &self,
        transitive_edges: &[(RenderNodeId, RenderNodeId)],
    ) -> String {
        let mut message = String::from("hierarchy contains redundant edge(s)");
        for &(parent, child) in transitive_edges {
            writeln!(
                message,
                " -- {} `{}` cannot be child of set `{}`, longer path exists",
                child.type_name(),
                self.get_node_name(child),
                self.get_node_name(parent),
            )
            .unwrap();
        }

        message
    }

    fn check_for_cross_dependencies(
        &self,
        dep_results: &CheckGraphResults<RenderNodeId>,
        hier_results_connected: &HashSet<(RenderNodeId, RenderNodeId)>,
    ) -> Result<(), RenderGraphError> {
        for &(a, b) in &dep_results.connected {
            if hier_results_connected.contains(&(a, b)) || hier_results_connected.contains(&(b, a))
            {
                let name_a = self.get_node_name(a);
                let name_b = self.get_node_name(b);
                return Err(RenderGraphError::CrossDependency(name_a, name_b));
            }
        }

        Ok(())
    }
}

impl ScheduleGraph for RenderGraph {
    type Id = RenderNodeId;
    type Executable = RenderGraphExecutable;
    type BuildError = RenderGraphError;
    type BuildSettings = RenderGraphBuildSettings;
    type ExecutorKind = ();
    type GlobalMetadata = ();

    fn new_executor(kind: Self::ExecutorKind) -> Box<dyn ScheduleExecutor<Self>> {
        todo!()
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
        for sys_idx in self.uninit.drain(..) {
            self.systems[sys_idx].get_mut().unwrap().initialize(world);
        }
    }

    fn update(
        &mut self,
        world: &mut World,
        executable: &mut Self::Executable,
        (): &Self::GlobalMetadata,
        label: InternedScheduleLabel,
    ) -> std::result::Result<(), Self::BuildError> {
        if !self.uninit.is_empty() {
            return Err(RenderGraphError::Uninitialized);
        }

        // Move systems out of old executable
        for (id, system) in executable
            .system_ids
            .drain(..)
            .zip(executable.systems.drain(..))
        {
            self.systems[id].inner = Some(system);
        }

        *executable = self.build_schedule(world, label)?;

        // Move systems into new executable
        for &id in &executable.system_ids {
            let system = self.systems[id].inner.take().unwrap();
            executable.systems.push(system);
        }

        Ok(())
    }
}

#[derive(Clone)]
pub struct RenderGraphBuildSettings {
    /// Determines whether the presence of redundant edges in the hierarchy of system sets is only
    /// logged or also results in a [`HierarchyRedundancy`](ScheduleBuildError::HierarchyRedundancy)
    /// error.
    ///
    /// Defaults to [`LogLevel::Warn`].
    pub hierarchy_detection: LogLevel,
    pub use_shortnames: bool,
    pub report_sets: bool,
}

impl Default for RenderGraphBuildSettings {
    fn default() -> Self {
        Self {
            hierarchy_detection: LogLevel::Warn,
            use_shortnames: true,
            report_sets: true,
        }
    }
}

#[derive(Default)]
pub struct RenderGraphExecutable {
    system_ids: Vec<usize>,
    systems: Vec<RenderSystem>,
}

impl ScheduleExecutable for RenderGraphExecutable {
    fn apply_deferred(&mut self, world: &mut World) {
        for system in &mut self.systems {
            system.apply_deferred(world);
        }
    }

    fn check_change_ticks(&mut self, change_tick: Tick) {
        for system in &mut self.systems {
            system.check_change_tick(change_tick);
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum RenderGraphError {
    /// A system set contains itself.
    #[error("System set `{0}` contains itself.")]
    HierarchyLoop(String),
    /// The hierarchy of system sets contains a cycle.
    #[error("System set hierarchy contains cycle(s).\n{0}")]
    HierarchyCycle(String),
    /// The hierarchy of system sets contains redundant edges.
    ///
    /// This error is disabled by default, but can be opted-in using [`RenderGraphBuildSettings`].
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
    #[error("RenderGraph is not initialized")]
    Uninitialized,
}

pub type RenderSystem = BoxedReadOnlySystem<RenderCtx<'static>, Result<CommandBuffer>>;

pub struct RenderNode {
    inner: Option<RenderSystem>,
}

impl RenderNode {
    /// Create a new [`SystemNode`]
    pub fn new(system: RenderSystem) -> Self {
        Self {
            inner: Some(system),
        }
    }

    /// Obtain a reference to the [`RenderSystem`] represented by this node.
    pub fn get(&self) -> Option<&RenderSystem> {
        self.inner.as_ref()
    }

    /// Obtain a mutable reference to the [`RenderSystem`] represented by this node.
    pub fn get_mut(&mut self) -> Option<&mut RenderSystem> {
        self.inner.as_mut()
    }
}

pub struct RenderCtx<'a> {
    _marker: PhantomData<&'a ()>,
}

impl SystemInput for RenderCtx<'_> {
    type Param<'i> = RenderCtx<'i>;
    type Inner<'i> = RenderCtx<'i>;

    fn wrap(this: Self::Inner<'_>) -> Self::Param<'_> {
        this
    }
}
