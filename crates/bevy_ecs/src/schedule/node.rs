use alloc::{sync::Arc, vec::Vec};
use bevy_utils::prelude::DebugName;
use core::ops::{DerefMut, Index, Range};

use bevy_platform::{collections::HashMap, sync::Mutex};
use slotmap::{new_key_type, SecondaryMap, SlotMap};

use crate::{
    component::{CheckChangeTicks, ComponentId, Tick},
    prelude::{SystemIn, SystemSet},
    query::FilteredAccessSet,
    schedule::InternedSystemSet,
    system::{
        IntoSystem, ReadOnlySystem, RunSystemError, System, SystemParamValidationError,
        SystemStateFlags,
    },
    world::{unsafe_world_cell::UnsafeWorldCell, DeferredWorld, World},
};

/// A wrapper around a system that provides access to it and its access set.
pub struct WithAccess<S: System + ?Sized> {
    /// The access returned by [`System::initialize`](crate::system::System::initialize).
    /// This will be empty if the system has not been initialized yet.
    pub access: FilteredAccessSet<ComponentId>,
    /// The system itself.
    pub system: S,
}

impl<S: System> WithAccess<S> {
    /// Constructs a new [`WithAccess`] from a [`System`].
    /// The `access` will initially be empty.
    pub fn new(system: S) -> Self {
        Self {
            access: FilteredAccessSet::new(),
            system,
        }
    }
}

impl<S: System + ?Sized> System for WithAccess<S> {
    type In = S::In;
    type Out = S::Out;

    #[inline]
    fn name(&self) -> DebugName {
        self.system.name()
    }

    #[inline]
    fn flags(&self) -> SystemStateFlags {
        self.system.flags()
    }

    #[inline]
    unsafe fn run_unsafe(
        &mut self,
        input: SystemIn<'_, Self>,
        world: UnsafeWorldCell,
    ) -> Result<Self::Out, RunSystemError> {
        self.system.run_unsafe(input, world)
    }

    #[inline]
    fn apply_deferred(&mut self, world: &mut World) {
        self.system.apply_deferred(world);
    }

    #[inline]
    fn queue_deferred(&mut self, world: DeferredWorld) {
        self.system.queue_deferred(world);
    }

    #[inline]
    unsafe fn validate_param_unsafe(
        &mut self,
        world: UnsafeWorldCell,
    ) -> Result<(), SystemParamValidationError> {
        self.system.validate_param_unsafe(world)
    }

    #[inline]
    fn initialize(&mut self, world: &mut World) -> FilteredAccessSet<ComponentId> {
        self.access = self.system.initialize(world);
        self.access.clone()
    }

    #[inline]
    fn check_change_tick(&mut self, check: CheckChangeTicks) {
        self.system.check_change_tick(check);
    }

    #[inline]
    fn default_system_sets(&self) -> Vec<InternedSystemSet> {
        self.system.default_system_sets()
    }

    #[inline]
    fn get_last_run(&self) -> Tick {
        self.system.get_last_run()
    }

    #[inline]
    fn set_last_run(&mut self, last_run: Tick) {
        self.system.set_last_run(last_run);
    }
}

/// A wrapper around a system that provides access to it via an `Arc<Mutex<_>>`.
pub struct SystemArc<S: System + ?Sized = dyn System<In = (), Out = ()>>(Arc<Mutex<WithAccess<S>>>);

/// A wrapper around a condition that provides access to it via an `Arc<Mutex<_>>`.
pub type ConditionArc<In = ()> = SystemArc<dyn ReadOnlySystem<In = In, Out = bool>>;

impl<S: System> SystemArc<S> {
    /// Converts a system into a [`SystemArc`].
    pub fn new<M>(
        system: impl IntoSystem<S::In, S::Out, M, System = S>,
    ) -> SystemArc<dyn System<In = S::In, Out = S::Out>> {
        SystemArc(Arc::new(Mutex::new(WithAccess::new(
            IntoSystem::into_system(system),
        ))))
    }
}

impl<S: ReadOnlySystem> SystemArc<S> {
    /// Converts a read-only system into a [`SystemArc`].
    pub fn new_readonly<M>(
        system: impl IntoSystem<S::In, S::Out, M, System = S>,
    ) -> SystemArc<dyn ReadOnlySystem<In = S::In, Out = S::Out>> {
        SystemArc(Arc::new(Mutex::new(WithAccess::new(
            IntoSystem::into_system(system),
        ))))
    }
}

impl<S: System + ?Sized> SystemArc<S> {
    /// Initializes the system and stores its access.
    pub fn initialize(&self, world: &mut World) {
        let mut system = self.lock();
        system.access = system.system.initialize(world);
    }

    /// Acquires a lock on the system, allowing access to it.
    pub fn lock(&self) -> impl DerefMut<Target = WithAccess<S>> + '_ {
        self.0.try_lock().unwrap()
    }
}

impl<S: System + ?Sized> Clone for SystemArc<S> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

new_key_type! {
    /// A unique identifier for a system in a [`ScheduleGraph`].
    pub struct SystemKey;
    /// A unique identifier for a system set in a [`ScheduleGraph`].
    pub struct SystemSetKey;
}

/// Container for systems in a schedule.
#[derive(Default)]
pub struct Systems {
    /// List of systems in the schedule.
    nodes: SlotMap<SystemKey, SystemArc>,
    /// List of conditions for each system, in the same order as `nodes`.
    conditions: SecondaryMap<SystemKey, Vec<ConditionArc>>,
    /// Systems and their conditions that have not been initialized yet.
    uninit: Vec<SystemKey>,
}

impl Systems {
    /// Returns the number of systems in this container.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns `true` if this container is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns a reference to the system with the given key, if it exists.
    pub fn get(&self, key: SystemKey) -> Option<&SystemArc> {
        self.nodes.get(key)
    }

    /// Returns `true` if the system with the given key has conditions.
    pub fn has_conditions(&self, key: SystemKey) -> bool {
        self.conditions
            .get(key)
            .is_some_and(|conditions| !conditions.is_empty())
    }

    /// Returns a reference to the conditions for the system with the given key, if it exists.
    pub fn get_conditions(&self, key: SystemKey) -> Option<&[ConditionArc]> {
        self.conditions.get(key).map(Vec::as_slice)
    }

    /// Returns a mutable reference to the conditions for the system with the given key, if it exists.
    pub fn get_conditions_mut(&mut self, key: SystemKey) -> Option<&mut Vec<ConditionArc>> {
        self.conditions.get_mut(key)
    }

    /// Returns an iterator over all systems and their conditions in this
    /// container.
    pub fn iter(&self) -> impl Iterator<Item = (SystemKey, &SystemArc, &[ConditionArc])> + '_ {
        self.nodes.iter().map(|(key, system)| {
            let conditions = self
                .conditions
                .get(key)
                .map(Vec::as_slice)
                .unwrap_or_default();
            (key, system, conditions)
        })
    }

    /// Inserts a new system into the container, along with its conditions,
    /// and queues it to be initialized later in [`Systems::initialize`].
    ///
    /// We have to defer initialization of systems in the container until we have
    /// `&mut World` access, so we store these in a list until
    /// [`Systems::initialize`] is called. This is usually done upon the first
    /// run of the schedule.
    pub fn insert(&mut self, system: SystemArc, conditions: Vec<ConditionArc>) -> SystemKey {
        let key = self.nodes.insert(system);
        self.conditions.insert(key, conditions);
        self.uninit.push(key);
        key
    }

    /// Returns `true` if all systems in this container have been initialized.
    pub fn is_initialized(&self) -> bool {
        self.uninit.is_empty()
    }

    /// Initializes all systems and their conditions that have not been
    /// initialized yet.
    pub fn initialize(&mut self, world: &mut World) {
        for key in self.uninit.drain(..) {
            if let Some(system) = self.nodes.get(key) {
                system.initialize(world);
            }
            if let Some(conditions) = self.conditions.get(key) {
                for condition in conditions {
                    condition.initialize(world);
                }
            }
        }
    }
}

impl Index<SystemKey> for Systems {
    type Output = SystemArc;

    #[track_caller]
    fn index(&self, key: SystemKey) -> &Self::Output {
        self.get(key)
            .unwrap_or_else(|| panic!("System with key {:?} does not exist in the schedule", key))
    }
}

/// Container for system sets in a schedule.
#[derive(Default)]
pub struct SystemSets {
    /// List of system sets in the schedule.
    sets: SlotMap<SystemSetKey, InternedSystemSet>,
    /// List of conditions for each system set, in the same order as `sets`.
    conditions: SecondaryMap<SystemSetKey, Vec<ConditionArc>>,
    /// Map from system sets to their keys.
    ids: HashMap<InternedSystemSet, SystemSetKey>,
    /// System sets that have not been initialized yet.
    uninit: Vec<UninitializedSet>,
}

/// A system set's conditions that have not been initialized yet.
struct UninitializedSet {
    key: SystemSetKey,
    /// The range of indices in [`SystemSets::conditions`] that correspond
    /// to conditions that have not been initialized yet.
    ///
    /// [`SystemSets::conditions`] for a given set may be appended to
    /// multiple times (e.g. when `configure_sets` is called multiple with
    /// the same set), so we need to track which conditions in that list
    /// are newly added and not yet initialized.
    ///
    /// Systems don't need this tracking because each `add_systems` call
    /// creates separate nodes in the graph with their own conditions,
    /// so all conditions are initialized together.
    uninitialized_conditions: Range<usize>,
}

impl SystemSets {
    /// Returns the number of system sets in this container.
    pub fn len(&self) -> usize {
        self.sets.len()
    }

    /// Returns `true` if this container is empty.
    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
    }

    /// Returns `true` if the given set is present in this container.
    pub fn contains(&self, set: impl SystemSet) -> bool {
        self.ids.contains_key(&set.intern())
    }

    /// Returns a reference to the system set with the given key, if it exists.
    pub fn get(&self, key: SystemSetKey) -> Option<&dyn SystemSet> {
        self.sets.get(key).map(|set| &**set)
    }

    /// Returns the key for the given system set, inserting it into this
    /// container if it does not already exist.
    pub fn get_key_or_insert(&mut self, set: InternedSystemSet) -> SystemSetKey {
        *self.ids.entry(set).or_insert_with(|| {
            let key = self.sets.insert(set);
            self.conditions.insert(key, Vec::new());
            key
        })
    }

    /// Returns `true` if the system set with the given key has conditions.
    pub fn has_conditions(&self, key: SystemSetKey) -> bool {
        self.conditions
            .get(key)
            .is_some_and(|conditions| !conditions.is_empty())
    }

    /// Returns a reference to the conditions for the system set with the given
    /// key, if it exists.
    pub fn get_conditions(&self, key: SystemSetKey) -> Option<&[ConditionArc]> {
        self.conditions.get(key).map(Vec::as_slice)
    }

    /// Returns a mutable reference to the conditions for the system set with
    /// the given key, if it exists.
    pub fn get_conditions_mut(&mut self, key: SystemSetKey) -> Option<&mut Vec<ConditionArc>> {
        self.conditions.get_mut(key)
    }

    /// Returns an iterator over all system sets in this container, along with
    /// their conditions.
    pub fn iter(&self) -> impl Iterator<Item = (SystemSetKey, &dyn SystemSet, &[ConditionArc])> {
        self.sets.iter().filter_map(|(key, set)| {
            let conditions = self.conditions.get(key)?.as_slice();
            Some((key, &**set, conditions))
        })
    }

    /// Inserts conditions for a system set into the container, and queues the
    /// newly added conditions to be initialized later in [`SystemSets::initialize`].
    ///
    /// If the set was not already present in the container, it is added automatically.
    ///
    /// We have to defer initialization of system set conditions in the container
    /// until we have `&mut World` access, so we store these in a list until
    /// [`SystemSets::initialize`] is called. This is usually done upon the
    /// first run of the schedule.
    pub fn insert(
        &mut self,
        set: InternedSystemSet,
        mut new_conditions: Vec<ConditionArc>,
    ) -> SystemSetKey {
        let key = self.get_key_or_insert(set);
        if !new_conditions.is_empty() {
            let current_conditions = &mut self.conditions[key];
            let start = current_conditions.len();
            self.uninit.push(UninitializedSet {
                key,
                uninitialized_conditions: start..(start + new_conditions.len()),
            });
            current_conditions.append(&mut new_conditions);
        }
        key
    }

    /// Returns `true` if all system sets' conditions in this container have
    /// been initialized.
    pub fn is_initialized(&self) -> bool {
        self.uninit.is_empty()
    }

    /// Initializes all system sets' conditions that have not been
    /// initialized yet. Because a system set's conditions may be appended to
    /// multiple times, we track which conditions were added since the last
    /// initialization and only initialize those.
    pub fn initialize(&mut self, world: &mut World) {
        for uninit in self.uninit.drain(..) {
            if let Some(conditions) = self.conditions.get(uninit.key) {
                for condition in &conditions[uninit.uninitialized_conditions] {
                    condition.initialize(world);
                }
            }
        }
    }
}

impl Index<SystemSetKey> for SystemSets {
    type Output = dyn SystemSet;

    #[track_caller]
    fn index(&self, key: SystemSetKey) -> &Self::Output {
        self.get(key).unwrap_or_else(|| {
            panic!(
                "System set with key {:?} does not exist in the schedule",
                key
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use crate::{
        prelude::SystemSet,
        schedule::{SystemArc, SystemSets, Systems},
        system::IntoSystem,
        world::World,
    };

    #[derive(SystemSet, Clone, Copy, PartialEq, Eq, Debug, Hash)]
    pub struct TestSet;

    #[test]
    fn systems() {
        fn empty_system() {}

        let mut systems = Systems::default();
        assert!(systems.is_empty());
        assert_eq!(systems.len(), 0);

        let system = SystemArc::new(IntoSystem::into_system(empty_system));
        let key = systems.insert(system, vec![]);

        assert!(!systems.is_empty());
        assert_eq!(systems.len(), 1);
        assert!(systems.get(key).is_some());
        assert!(systems.get_conditions(key).is_some());
        assert!(systems.get_conditions(key).unwrap().is_empty());
        assert!(!systems.is_initialized());
        assert!(systems.iter().next().is_some());

        let mut world = World::new();
        systems.initialize(&mut world);
        assert!(systems.is_initialized());
    }

    #[test]
    fn system_sets() {
        fn always_true() -> bool {
            true
        }

        let mut sets = SystemSets::default();
        assert!(sets.is_empty());
        assert_eq!(sets.len(), 0);

        let condition = SystemArc::new_readonly(IntoSystem::into_system(always_true));
        let key = sets.insert(TestSet.intern(), vec![condition]);

        assert!(!sets.is_empty());
        assert_eq!(sets.len(), 1);
        assert!(sets.get(key).is_some());
        assert!(sets.get_conditions(key).is_some());
        assert!(!sets.get_conditions(key).unwrap().is_empty());
        assert!(!sets.is_initialized());
        assert!(sets.iter().next().is_some());

        let mut world = World::new();
        sets.initialize(&mut world);
        assert!(sets.is_initialized());
    }
}
