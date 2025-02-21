use alloc::boxed::Box;

use bevy_platform_support::collections::HashMap;

use crate::{
    component::Tick,
    resource::Resource,
    result::{DefaultSystemErrorHandler, Error, SystemErrorContext},
    schedule2::{
        DefaultGraph, GraphNode, InternedScheduleLabel, IntoNodeConfigs, ScheduleBuildPass,
        ScheduleExecutable, ScheduleExecutor, ScheduleGraph, ScheduleLabel,
    },
    world::World,
};

/// Resource that stores [`Schedule`]s mapped to [`ScheduleLabel`]s excluding the current running [`Schedule`].
#[derive(Resource, Default)]
pub struct Schedules<G: ScheduleGraph = DefaultGraph> {
    inner: HashMap<InternedScheduleLabel, Schedule<G>>,
    /// Metadata shared between all schedules.
    pub metadata: G::GlobalMetadata,
}

impl<G: ScheduleGraph> Schedules<G> {
    /// Inserts a labeled schedule into the map.
    ///
    /// If the map already had an entry for `label`, `schedule` is inserted,
    /// and the old schedule is returned. Otherwise, `None` is returned.
    pub fn insert(&mut self, schedule: Schedule<G>) -> Option<Schedule<G>> {
        self.inner.insert(schedule.label, schedule)
    }

    /// Removes the schedule corresponding to the `label` from the map, returning it if it existed.
    pub fn remove(&mut self, label: impl ScheduleLabel) -> Option<Schedule<G>> {
        self.inner.remove(&label.intern())
    }

    /// Does a schedule with the provided label already exist?
    pub fn contains(&self, label: impl ScheduleLabel) -> bool {
        self.inner.contains_key(&label.intern())
    }

    /// Returns a reference to the schedule associated with `label`, if it exists.
    pub fn get(&self, label: impl ScheduleLabel) -> Option<&Schedule<G>> {
        self.inner.get(&label.intern())
    }

    /// Returns a mutable reference to the schedule associated with `label`, if it exists.
    pub fn get_mut(&mut self, label: impl ScheduleLabel) -> Option<&mut Schedule<G>> {
        self.inner.get_mut(&label.intern())
    }

    /// Returns a mutable reference to the schedules associated with `label`, creating one if it doesn't already exist.
    pub fn entry(&mut self, label: impl ScheduleLabel) -> &mut Schedule<G> {
        self.inner
            .entry(label.intern())
            .or_insert_with(|| Schedule::new(label))
    }

    /// Returns an iterator over all schedules. Iteration order is undefined.
    pub fn iter(&self) -> impl Iterator<Item = (&dyn ScheduleLabel, &Schedule<G>)> {
        self.inner
            .iter()
            .map(|(label, schedule)| (&**label, schedule))
    }

    /// Returns an iterator over mutable references to all schedules. Iteration order is undefined.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&dyn ScheduleLabel, &mut Schedule<G>)> {
        self.inner
            .iter_mut()
            .map(|(label, schedule)| (&**label, schedule))
    }

    /// Iterates the change ticks of all systems in all stored schedules and clamps any older than
    /// [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    pub(crate) fn check_change_ticks(&mut self, change_tick: Tick) {
        #[cfg(feature = "trace")]
        let _all_span = info_span!("check stored schedule ticks").entered();
        #[cfg_attr(
            not(feature = "trace"),
            expect(
                unused_variables,
                reason = "The `label` variable goes unused if the `trace` feature isn't active"
            )
        )]
        for (label, schedule) in &mut self.inner {
            #[cfg(feature = "trace")]
            let name = format!("{label:?}");
            #[cfg(feature = "trace")]
            let _one_span = info_span!("check schedule ticks", name = &name).entered();
            schedule.check_change_ticks(change_tick);
        }
    }

    /// Applies the provided [`ScheduleBuildSettings`] to all schedules.
    pub fn configure_schedules(&mut self, schedule_build_settings: G::BuildSettings) {
        for (_, schedule) in &mut self.inner {
            schedule.set_build_settings(schedule_build_settings.clone());
        }
    }

    /// Adds one or more nodes to the [`Schedule`] matching the provided [`ScheduleLabel`].
    pub fn add_nodes<N: GraphNode<Graph = G>, M>(
        &mut self,
        schedule: impl ScheduleLabel,
        systems: impl IntoNodeConfigs<N, M>,
    ) -> &mut Self {
        self.entry(schedule).process_configs(systems);
        self
    }

    // TODO: ignore_ambiguity
}

/// A collection of systems, and the metadata and executor needed to run them
/// in a certain order under certain conditions.
///
/// # Example
/// Here is an example of a `Schedule` running a "Hello world" system:
/// ```
/// # use bevy_ecs::prelude::*;
/// fn hello_world() { println!("Hello world!") }
///
/// fn main() {
///     let mut world = World::new();
///     let mut schedule = Schedule::default();
///     schedule.add_systems(hello_world);
///
///     schedule.run(&mut world);
/// }
/// ```
///
/// A schedule can also run several systems in an ordered way:
/// ```
/// # use bevy_ecs::prelude::*;
/// fn system_one() { println!("System 1 works!") }
/// fn system_two() { println!("System 2 works!") }
/// fn system_three() { println!("System 3 works!") }
///
/// fn main() {
///     let mut world = World::new();
///     let mut schedule = Schedule::default();
///     schedule.add_systems((
///         system_two,
///         system_one.before(system_two),
///         system_three.after(system_two),
///     ));
///
///     schedule.run(&mut world);
/// }
/// ```
pub struct Schedule<G: ScheduleGraph = DefaultGraph> {
    label: InternedScheduleLabel,
    graph: G,
    executable: G::Executable,
    executor: Box<dyn ScheduleExecutor<G>>,
    executor_initialized: bool,
    error_handler: Option<fn(Error, SystemErrorContext)>,
}

impl<G: ScheduleGraph> Schedule<G> {
    /// Creates an empty schedule.
    pub fn new(label: impl ScheduleLabel) -> Self {
        Self {
            label: label.intern(),
            graph: G::default(),
            executable: G::Executable::default(),
            executor: G::new_executor(G::ExecutorKind::default()),
            executor_initialized: false,
            error_handler: None,
        }
    }

    /// Returns the [`ScheduleLabel`] for this schedule.
    pub fn label(&self) -> impl ScheduleLabel {
        self.label
    }

    /// Returns a read-only reference to this schedule's graph.
    pub fn graph(&self) -> &G {
        &self.graph
    }

    /// Returns a mutable reference to this schedule's graph.
    pub fn graph_mut(&mut self) -> &mut G {
        &mut self.graph
    }

    /// Returns a read-only reference to this schedule's executable.
    pub fn executable(&self) -> &G::Executable {
        &self.executable
    }

    /// Processes a collection of node configurations for the schedule's graph.
    pub fn process_configs<N: GraphNode<Graph = G>, M>(
        &mut self,
        nodes: impl IntoNodeConfigs<N, M>,
    ) -> &mut Self {
        let label = self.label;
        self.try_process_configs(nodes)
            .unwrap_or_else(|e| panic!("Error when processing schedule {:?} configs: {e}", label))
    }

    /// Processes a collection of node configurations for the schedule's graph.
    pub fn try_process_configs<N: GraphNode<Graph = G>, M>(
        &mut self,
        nodes: impl IntoNodeConfigs<N, M>,
    ) -> Result<&mut Self, G::BuildError> {
        N::process_configs(&mut self.graph, nodes.into_configs(), false)?;
        Ok(self)
    }

    /// Adds a custom build pass to the schedule.
    pub fn add_build_pass<P: ScheduleBuildPass<G>>(&mut self, pass: P) -> &mut Self {
        self.graph.add_build_pass(pass);
        self
    }

    /// Removes a custom build pass from the schedule.
    pub fn remove_build_pass<P: ScheduleBuildPass<G>>(&mut self) {
        self.graph.remove_build_pass::<P>();
    }

    /// Returns the schedule's current build settings.
    pub fn get_build_settings(&self) -> &G::BuildSettings {
        self.graph.get_build_settings()
    }

    /// Changes miscellaneous build settings.
    pub fn set_build_settings(&mut self, settings: G::BuildSettings) -> &mut Self {
        self.graph.set_build_settings(settings);
        self
    }

    /// Returns the schedule's current execution strategy.
    pub fn get_executor_kind(&self) -> G::ExecutorKind {
        self.executor.kind()
    }

    /// Sets the schedule's execution strategy.
    pub fn set_executor_kind(&mut self, executor: G::ExecutorKind) -> &mut Self {
        if executor != self.executor.kind() {
            self.executor = G::new_executor(executor);
            self.executor_initialized = false;
        }
        self
    }

    /// Set the error handler to use for systems that return a
    /// [`Result`](crate::result::Result).
    ///
    /// See the [`result` module-level documentation](crate::result) for more
    /// information.
    pub fn set_error_handler(&mut self, error_handler: fn(Error, SystemErrorContext)) -> &mut Self {
        self.error_handler = Some(error_handler);
        self
    }

    /// Set whether the schedule applies deferred system buffers on final time
    /// or not. This is a catch-all in case a system uses commands but was not
    /// explicitly ordered before an instance of [`ApplyDeferred`]. By default
    /// this setting is true, but may be disabled if needed.
    pub fn set_apply_final_deferred(&mut self, value: bool) -> &mut Self {
        self.executor.set_apply_final_deferred(value);
        self
    }

    /// Runs all systems in this schedule on the `world`, using its current
    /// execution strategy.
    pub fn run(&mut self, world: &mut World) {
        #[cfg(feature = "trace")]
        let _span = info_span!("schedule", name = ?self.label).entered();

        world.check_change_ticks();
        self.initialize(world)
            .unwrap_or_else(|e| panic!("Error when initializing schedule {:?}: {e}", self.label));

        let error_handler = self
            .error_handler
            .unwrap_or_else(|| unreachable!("schedule initialized"));

        // TODO: bevy_debug_stepping

        self.executor
            .run(&mut self.executable, world, error_handler);
    }

    /// Initializes any newly-added systems and conditions, rebuilds the
    /// executable schedule, and re-initializes the executor.
    ///
    /// Moves all systems and run conditions out of the [`ScheduleGraph`].
    pub fn initialize(&mut self, world: &mut World) -> Result<(), G::BuildError> {
        if self.graph.changed() {
            self.graph.initialize(world);
            let global_metadata = world
                .get_resource_or_init::<Schedules<G>>()
                .metadata
                .clone();
            self.graph
                .update(world, &mut self.executable, &global_metadata, self.label)?;
            self.graph.set_changed(false);
            self.executor_initialized = false;
        }

        if self.error_handler.is_none() {
            self.error_handler = Some(world.get_resource_or_init::<DefaultSystemErrorHandler>().0);
        }

        if !self.executor_initialized {
            self.executor.initialize(&self.executable);
            self.executor_initialized = true;
        }

        Ok(())
    }

    /// Directly applies any accumulated [`Deferred`](crate::system::Deferred)
    /// system parameters (like [`Commands`](crate::prelude::Commands)) to the
    /// `world`.
    ///
    /// Like always, deferred system parameters are applied in the "topological
    /// sort order" of the schedule graph. As a result, buffers from one system
    /// are only guaranteed to be applied before those of other systems if there
    /// is an explicit system ordering between the two systems.
    ///
    /// This is used in rendering to extract data from the main world, storing
    /// the data in system buffers, before applying their buffers in a different
    /// world.
    pub fn apply_deferred(&mut self, world: &mut World) {
        self.executable.apply_deferred(world);
    }

    /// Iterates the change ticks of all nodes in the schedule and clamps any
    /// older than [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    pub(crate) fn check_change_ticks(&mut self, change_tick: Tick) {
        self.executable.check_change_ticks(change_tick);
    }
}
