use std::{any::TypeId, collections::BTreeMap, marker::PhantomData};

use bevy_ecs::{
    component::Tick,
    result::Result,
    schedule::{
        graph::{Dag, Direction},
        traits::{ScheduleExecutable, ScheduleGraph},
        AnonymousSet, InternedSystemSet, NodeConfig, ScheduleBuildPass, ScheduleBuildPassObj,
        ScheduleExecutor,
    },
    system::{BoxedReadOnlySystem, SystemInput},
    world::World,
};
use bevy_platform_support::collections::HashMap;
use wgpu::CommandBuffer;

use crate::render_graph2::{node::RenderNodeId, FallibleRenderSystem};

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
    uninit: Vec<usize>,
    /// Directed acyclic graph of the hierarchy (which systems/sets are children of which sets)
    hierarchy: Dag<RenderNodeId>,
    /// Directed acyclic graph of the dependency (which systems/sets have to run before which other systems/sets)
    dependency: Dag<RenderNodeId>,
    anonymous_sets: usize,
    changed: bool,
    passes: BTreeMap<TypeId, Box<dyn ScheduleBuildPassObj<Self>>>,
}

// impl RenderGraph {
//     /// Add a single render system config to the graph, including its dependencies.
//     pub(crate) fn add_system_inner(
//         &mut self,
//         config: NodeConfig<FallibleRenderSystem, Self>,
//     ) -> Result<RenderNodeId, RenderGraphError> {
//         let id = RenderNodeId::System(self.systems.len());

//         // graph updates are immediate
//         self.update_graphs(id, config.metadata.graph_info)?;

//         // system init has to be deferred (need `&mut World`)
//         self.uninit.push(id.index());
//         self.systems.push(RenderNode::new(config.node.0));

//         Ok(id)
//     }

//     /// Checks that a system set isn't included in itself.
//     /// If not present, add the set to the graph.
//     fn check_hierarchy_set(
//         &mut self,
//         id: &RenderNodeId,
//         set: InternedSystemSet,
//     ) -> Result<(), RenderGraphError> {
//         match self.system_set_ids.get(&set) {
//             Some(set_id) => {
//                 if id == set_id {
//                     return Err(RenderGraphError::HierarchyLoop(self.get_node_name(id)));
//                 }
//             }
//             None => {
//                 self.add_set(set);
//             }
//         }

//         Ok(())
//     }

//     fn create_anonymous_set(&mut self) -> AnonymousSet {
//         let id = self.anonymous_sets;
//         self.anonymous_sets += 1;
//         AnonymousSet::new(id)
//     }

//     /// Check that no set is included in itself.
//     /// Add all the sets from the [`GraphInfo`]'s hierarchy to the graph.
//     fn check_hierarchy_sets(
//         &mut self,
//         id: &RenderNodeId,
//         graph_info: &GraphInfo,
//     ) -> Result<(), RenderGraphError> {
//         for &set in &graph_info.hierarchy {
//             self.check_hierarchy_set(id, set)?;
//         }

//         Ok(())
//     }

//     fn get_node_name(&self, id: &RenderNodeId) -> String {
//         self.get_node_name_inner(id, self.settings.report_sets)
//     }

//     #[inline]
//     fn get_node_name_inner(&self, id: &RenderNodeId, report_sets: bool) -> String {
//         let name = match id {
//             RenderNodeId::System(_) => {
//                 let name = self.systems[id.index()].get().unwrap().name().to_string();
//                 if report_sets {
//                     let sets = self.names_of_sets_containing_node(id);
//                     if sets.is_empty() {
//                         name
//                     } else if sets.len() == 1 {
//                         format!("{name} (in set {})", sets[0])
//                     } else {
//                         format!("{name} (in sets {})", sets.join(", "))
//                     }
//                 } else {
//                     name
//                 }
//             }
//             RenderNodeId::Set(_) => {
//                 let set = &self.system_sets[id.index()];
//                 if set.is_anonymous() {
//                     self.anonymous_set_name(id)
//                 } else {
//                     set.name()
//                 }
//             }
//         };
//         if self.settings.use_shortnames {
//             ShortName(&name).to_string()
//         } else {
//             name
//         }
//     }

//     fn anonymous_set_name(&self, id: &RenderNodeId) -> String {
//         format!(
//             "({})",
//             self.hierarchy
//                 .graph
//                 .edges_directed(*id, Direction::Outgoing)
//                 // never get the sets of the members or this will infinite recurse when the report_sets setting is on.
//                 .map(|(_, member_id)| self.get_node_name_inner(&member_id, false))
//                 .reduce(|a, b| format!("{a}, {b}"))
//                 .unwrap_or_default()
//         )
//     }
// }

impl ScheduleGraph for RenderGraph {
    type Id = RenderNodeId;
    type Executable = RenderGraphExecutable;
    type BuildError = RenderGraphError;
    type BuildSettings = ();
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

    fn add_build_pass<P: ScheduleBuildPass<Self>>(&mut self, _pass: P) {
        todo!()
    }

    fn remove_build_pass<P: ScheduleBuildPass<Self>>(&mut self) {
        todo!()
    }

    fn get_build_settings(&self) -> &Self::BuildSettings {
        &()
    }

    fn set_build_settings(&mut self, (): Self::BuildSettings) {}

    fn initialize(&mut self, world: &mut World) {
        for sys_idx in self.uninit.drain(..) {
            self.systems[sys_idx].get_mut().unwrap().initialize(world);
        }
    }

    fn update(
        &mut self,
        world: &mut World,
        executable: &mut Self::Executable,
        global_metadata: &Self::GlobalMetadata,
        label: bevy_ecs::schedule::InternedScheduleLabel,
    ) -> std::result::Result<(), Self::BuildError> {
        if !self.uninit.is_empty() {
            return Err(RenderGraphError::Uninitialized);
        }

        todo!()
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
