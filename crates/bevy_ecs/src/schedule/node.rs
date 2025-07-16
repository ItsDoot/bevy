use alloc::{sync::Arc, vec::Vec};
use bevy_utils::prelude::DebugName;
use core::{
    any::TypeId,
    ops::{DerefMut, Index, Range},
};
use std::sync::{OnceLock, PoisonError};

use bevy_platform::{collections::HashMap, sync::Mutex};
use slotmap::{new_key_type, SecondaryMap, SlotMap};

use crate::{
    component::ComponentId,
    prelude::{ApplyDeferred, SystemSet},
    query::FilteredAccessSet,
    schedule::InternedSystemSet,
    system::{IntoSystem, ReadOnlySystem, System, SystemStateFlags},
    world::World,
};

/// A wrapper around a system that provides access to it via an `Arc<Mutex<_>>`.
pub struct SystemArc<S: System + ?Sized = dyn System<In = (), Out = ()>>(Arc<SystemArcInner<S>>);

struct SystemArcInner<S: System + ?Sized> {
    name: DebugName,
    flags: SystemStateFlags,
    type_id: TypeId,
    access: OnceLock<FilteredAccessSet<ComponentId>>,
    /// The system wrapped in a mutex for safe concurrent access.
    system: Mutex<S>,
}

/// A wrapper around a condition that provides access to it via an `Arc<Mutex<_>>`.
pub type ConditionArc<In = ()> = SystemArc<dyn ReadOnlySystem<In = In, Out = bool>>;

impl<S: System> SystemArc<S> {
    /// Converts a system into a [`SystemArc`].
    pub fn new<M>(
        system: impl IntoSystem<S::In, S::Out, M, System = S>,
    ) -> SystemArc<dyn System<In = S::In, Out = S::Out>> {
        let system = IntoSystem::into_system(system);
        let inner = SystemArcInner {
            name: system.name(),
            flags: system.flags(),
            type_id: system.type_id(),
            access: OnceLock::new(),
            system: Mutex::new(system),
        };
        SystemArc(Arc::new(inner))
    }
}

impl<S: ReadOnlySystem> SystemArc<S> {
    /// Converts a read-only system into a [`SystemArc`].
    pub fn new_readonly<M>(
        system: impl IntoSystem<S::In, S::Out, M, System = S>,
    ) -> SystemArc<dyn ReadOnlySystem<In = S::In, Out = S::Out>> {
        let system = IntoSystem::into_system(system);
        let inner = SystemArcInner {
            name: system.name(),
            flags: system.flags(),
            type_id: system.type_id(),
            access: OnceLock::new(),
            system: Mutex::new(system),
        };
        SystemArc(Arc::new(inner))
    }
}

impl<S: System + ?Sized> SystemArc<S> {
    /// Returns this system's name.
    #[inline]
    pub fn name(&self) -> &DebugName {
        &self.0.name
    }

    /// Returns the [`SystemStateFlags`] of this system.
    #[inline]
    pub fn flags(&self) -> SystemStateFlags {
        self.0.flags
    }

    /// Returns true if this system is [`Send`].
    #[inline]
    pub fn is_send(&self) -> bool {
        !self.flags().intersects(SystemStateFlags::NON_SEND)
    }

    /// Returns true if this system must be run exclusively.
    #[inline]
    pub fn is_exclusive(&self) -> bool {
        self.flags().intersects(SystemStateFlags::EXCLUSIVE)
    }

    /// Returns true if this system has deferred buffers.
    #[inline]
    pub fn has_deferred(&self) -> bool {
        self.flags().intersects(SystemStateFlags::DEFERRED)
    }

    /// Returns the [`TypeId`] of this system's underlying type.
    #[inline]
    pub fn type_id(&self) -> TypeId {
        self.0.type_id
    }

    /// Returns `true` if this [`System`] is an instance of [`ApplyDeferred`].
    #[inline]
    pub fn is_apply_deferred(&self) -> bool {
        self.type_id() == TypeId::of::<ApplyDeferred>()
    }

    /// Returns the [`FilteredAccessSet`] of this system, panicking if it has
    /// not been initialized yet.
    ///
    /// # Panics
    ///
    /// If the system has not been initialized yet, this will panic.
    pub fn access(&self) -> &FilteredAccessSet<ComponentId> {
        self.0.access.get().unwrap_or_else(|| {
            panic!(
                "System access for {:?} has not been initialized yet. Call `initialize` first.",
                self.name()
            )
        })
    }

    /// Returns the [`FilteredAccessSet`] of this system, or `None` if it has
    /// not been initialized yet.
    pub fn get_access(&self) -> Option<&FilteredAccessSet<ComponentId>> {
        self.0.access.get()
    }

    /// Initializes this system and stores its access.
    pub fn initialize(&self, world: &mut World) -> &FilteredAccessSet<ComponentId> {
        self.0
            .access
            .get_or_init(|| self.0.system.try_lock().unwrap().initialize(world))
    }

    /// Acquires a lock on this system, allowing access to it's [`System`].
    pub fn lock(&self) -> impl DerefMut<Target = S> + '_ {
        self.0.system.lock().unwrap_or_else(PoisonError::into_inner)
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
                assert!(
                    system.get_access().is_some(),
                    "System access should be initialized after calling `initialize`."
                );
            }
            if let Some(conditions) = self.conditions.get(key) {
                for condition in conditions {
                    condition.initialize(world);
                    assert!(
                        condition.get_access().is_some(),
                        "Condition access should be initialized after calling `initialize`."
                    );
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
