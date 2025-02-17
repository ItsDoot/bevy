//! Traits for indexing into ECS containers.

use alloc::vec::Vec;
use core::{error::Error, mem::MaybeUninit};

use bevy_platform_support::collections::{HashMap, HashSet};
use bevy_ptr::Ptr;

use crate::{
    component::ComponentId,
    entity::{hash_map::EntityHashMap, hash_set::EntityHashSet, Entity, EntityDoesNotExistError},
    world::{
        error::{EntityComponentError, EntityMutableFetchError},
        unsafe_world_cell::{UnsafeEntityCell, UnsafeWorldCell},
        DeferredWorld, EntityMut, EntityRef, EntityWorldMut, World,
    },
};

/// Trait for types that can be converted to their raw container with read-only access.
pub trait RawContainer {
    /// The raw container type.
    type Raw<'w>;
    /// The error type returned by calls to [`EcsCellIndex::get`].
    ///
    /// We define the error type here so that it is per-cell-type, not per-implementation.
    type Error<'w>: Error;
}

/// Trait for types that can be converted to their raw container with read-write access.
pub trait RawContainerMut {
    /// The raw container type.
    type Raw<'w>;
    /// The error type returned by calls to [`EcsCellIndexMut::get_mut`].
    ///
    /// We define the error type here so that it is per-cell-type, not per-implementation.
    type Error<'w>: Error;
}

impl RawContainer for World {
    type Raw<'w> = UnsafeWorldCell<'w>;
    type Error<'w> = EntityDoesNotExistError;
}

impl RawContainerMut for World {
    type Raw<'w> = UnsafeWorldCell<'w>;
    type Error<'w> = EntityMutableFetchError;
}

impl RawContainer for DeferredWorld<'_> {
    type Raw<'w> = UnsafeWorldCell<'w>;
    type Error<'w> = EntityDoesNotExistError;
}

impl RawContainerMut for DeferredWorld<'_> {
    type Raw<'w> = UnsafeWorldCell<'w>;
    type Error<'w> = EntityMutableFetchError;
}

impl RawContainer for EntityRef<'_> {
    type Raw<'w> = UnsafeEntityCell<'w>;
    type Error<'w> = EntityComponentError;
}

impl RawContainer for EntityMut<'_> {
    type Raw<'w> = UnsafeEntityCell<'w>;
    type Error<'w> = EntityComponentError;
}

impl RawContainerMut for EntityMut<'_> {
    type Raw<'w> = UnsafeEntityCell<'w>;
    type Error<'w> = EntityComponentError;
}

impl RawContainer for EntityWorldMut<'_> {
    type Raw<'w> = UnsafeEntityCell<'w>;
    type Error<'w> = EntityComponentError;
}

impl RawContainerMut for EntityWorldMut<'_> {
    type Raw<'w> = UnsafeEntityCell<'w>;
    type Error<'w> = EntityComponentError;
}

// impl<D: QueryData, F: QueryFilter> RawContainer for Query<'_, '_, D, F> {
//     type Raw<'w> = Query<'w, 'w, D::ReadOnly, F>;
//     type Error<'w> = QueryEntityError<'w>;
// }

// impl<D: QueryData, F: QueryFilter> RawContainerMut for Query<'_, '_, D, F> {
//     type Raw<'w> = Query<'w, 'w, D, F>;
//     type Error<'w> = QueryEntityError<'w>;
// }

/// Trait for types that can be used as a read-only index into the container `C`.
///
/// # Safety
///
/// Implementors must ensure that:
/// - No mutable references to the container are returned via [`EcsCellIndex::get`].
pub unsafe trait ContainerIndex<C: RawContainer> {
    /// The output type returned by indexing the container.
    type Output<'w>;

    /// Returns read-only reference(s) into the given raw container.
    ///
    /// # Safety
    ///
    /// It is the caller's responsibility to ensure that:
    /// - The given raw container has read-only access to the fetched data.
    /// - No mutable references to the fetched data exists at the same time.
    unsafe fn get(self, container: C::Raw<'_>) -> Result<Self::Output<'_>, C::Error<'_>>;
}

/// Trait for types that can be used as a read-write index into the container `C`.
pub trait ContainerIndexMut<C: RawContainerMut> {
    /// The output type returned by indexing the container.
    type Output<'w>;

    /// Returns mutable reference(s) into the given raw container.
    ///
    /// # Safety
    ///
    /// It is the caller's responsibility to ensure that:
    /// - The given raw container has mutable access to the fetched data.
    /// - No other mutable references to the fetched data exists at the same time.
    unsafe fn get_mut(self, container: C::Raw<'_>) -> Result<Self::Output<'_>, C::Error<'_>>;
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<World> for Entity {
    type Output<'w> = EntityRef<'w>;

    unsafe fn get(
        self,
        container: <World as RawContainer>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityDoesNotExistError> {
        let ecell = container.get_entity(self)?;
        // SAFETY: caller ensures that the world cell has read-only access to the entity.
        Ok(unsafe { EntityRef::new(ecell) })
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<World> for [Entity; N] {
    type Output<'w> = [EntityRef<'w>; N];

    unsafe fn get(
        self,
        container: <World as RawContainer>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityDoesNotExistError> {
        <&Self as ContainerIndex<World>>::get(&self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<World> for &'_ [Entity; N] {
    type Output<'w> = [EntityRef<'w>; N];

    unsafe fn get(
        self,
        container: <World as RawContainer>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityDoesNotExistError> {
        let mut refs = [MaybeUninit::uninit(); N];
        for (r, &id) in core::iter::zip(&mut refs, self) {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has read-only access to the entity.
            *r = MaybeUninit::new(unsafe { EntityRef::new(ecell) });
        }

        // SAFETY: Each item was initialized in the loop above.
        let refs = refs.map(|r| unsafe { MaybeUninit::assume_init(r) });
        Ok(refs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<World> for &'_ [Entity] {
    type Output<'w> = Vec<EntityRef<'w>>;

    unsafe fn get(
        self,
        container: <World as RawContainer>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityDoesNotExistError> {
        let mut refs = Vec::with_capacity(self.len());
        for &id in self {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has read-only access to the entity.
            refs.push(unsafe { EntityRef::new(ecell) });
        }
        Ok(refs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<World> for &'_ EntityHashSet {
    type Output<'w> = EntityHashMap<EntityRef<'w>>;

    unsafe fn get(
        self,
        container: <World as RawContainer>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityDoesNotExistError> {
        let mut refs = EntityHashMap::with_capacity(self.len());
        for &id in self {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has read-only access to the entity.
            refs.insert(id, unsafe { EntityRef::new(ecell) });
        }
        Ok(refs)
    }
}

impl ContainerIndexMut<World> for Entity {
    type Output<'w> = EntityWorldMut<'w>;

    unsafe fn get_mut(
        self,
        container: <World as RawContainerMut>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityMutableFetchError> {
        let location = container
            .entities()
            .get(self)
            .ok_or(EntityDoesNotExistError::new(self, container.entities()))?;
        // SAFETY: caller ensures that the world cell has mutable access to the entity.
        let world = unsafe { container.world_mut() };
        // SAFETY: location was fetched from the same world's `Entities`.
        Ok(unsafe { EntityWorldMut::new(world, self, location) })
    }
}

impl<const N: usize> ContainerIndexMut<World> for [Entity; N] {
    type Output<'w> = [EntityMut<'w>; N];

    unsafe fn get_mut(
        self,
        container: <World as RawContainerMut>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityMutableFetchError> {
        <&Self as ContainerIndexMut<World>>::get_mut(&self, container)
    }
}

impl<const N: usize> ContainerIndexMut<World> for &'_ [Entity; N] {
    type Output<'w> = [EntityMut<'w>; N];

    unsafe fn get_mut(
        self,
        container: <World as RawContainerMut>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityMutableFetchError> {
        // Check for duplicate entities.
        for i in 0..self.len() {
            for j in 0..i {
                if self[i] == self[j] {
                    return Err(EntityMutableFetchError::AliasedMutability(self[i]));
                }
            }
        }

        let mut refs = [const { MaybeUninit::uninit() }; N];
        for (r, &id) in core::iter::zip(&mut refs, self) {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has mutable access to the entity.
            *r = MaybeUninit::new(unsafe { EntityMut::new(ecell) });
        }

        // SAFETY: Each item was initialized in the loop above.
        let refs = refs.map(|r| unsafe { MaybeUninit::assume_init(r) });
        Ok(refs)
    }
}

impl ContainerIndexMut<World> for &'_ [Entity] {
    type Output<'w> = Vec<EntityMut<'w>>;

    unsafe fn get_mut(
        self,
        container: <World as RawContainerMut>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityMutableFetchError> {
        // Check for duplicate entities.
        for i in 0..self.len() {
            for j in 0..i {
                if self[i] == self[j] {
                    return Err(EntityMutableFetchError::AliasedMutability(self[i]));
                }
            }
        }

        let mut refs = Vec::with_capacity(self.len());
        for &id in self {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has mutable access to the entity.
            refs.push(unsafe { EntityMut::new(ecell) });
        }

        Ok(refs)
    }
}

impl ContainerIndexMut<World> for &'_ EntityHashSet {
    type Output<'w> = EntityHashMap<EntityMut<'w>>;

    unsafe fn get_mut(
        self,
        container: <World as RawContainerMut>::Raw<'_>,
    ) -> Result<Self::Output<'_>, EntityMutableFetchError> {
        let mut refs = EntityHashMap::with_capacity(self.len());
        for &id in self {
            let ecell = container.get_entity(id)?;
            // SAFETY: caller ensures that the world cell has mutable access to the entity.
            refs.insert(id, unsafe { EntityMut::new(ecell) });
        }
        Ok(refs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<DeferredWorld<'_>> for Entity {
    type Output<'w> = EntityRef<'w>;

    unsafe fn get<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityDoesNotExistError> {
        <Self as ContainerIndex<World>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<DeferredWorld<'_>> for [Entity; N] {
    type Output<'w> = [EntityRef<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityDoesNotExistError> {
        <&Self as ContainerIndex<DeferredWorld>>::get(&self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<DeferredWorld<'_>> for &'_ [Entity; N] {
    type Output<'w> = [EntityRef<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityDoesNotExistError> {
        <Self as ContainerIndex<World>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<DeferredWorld<'_>> for &'_ [Entity] {
    type Output<'w> = Vec<EntityRef<'w>>;

    unsafe fn get<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityDoesNotExistError> {
        <Self as ContainerIndex<World>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<DeferredWorld<'_>> for &'_ EntityHashSet {
    type Output<'w> = EntityHashMap<EntityRef<'w>>;

    unsafe fn get<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityDoesNotExistError> {
        <Self as ContainerIndex<World>>::get(self, container)
    }
}

impl ContainerIndexMut<DeferredWorld<'_>> for Entity {
    type Output<'w> = EntityMut<'w>;

    unsafe fn get_mut<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainerMut>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityMutableFetchError> {
        let ecell = container.get_entity(self)?;
        // SAFETY: caller ensures that the world cell has mutable access to the entity.
        Ok(unsafe { EntityMut::new(ecell) })
    }
}

impl<const N: usize> ContainerIndexMut<DeferredWorld<'_>> for [Entity; N] {
    type Output<'w> = [EntityMut<'w>; N];

    unsafe fn get_mut<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainerMut>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityMutableFetchError> {
        <&Self as ContainerIndexMut<DeferredWorld>>::get_mut(&self, container)
    }
}

impl<const N: usize> ContainerIndexMut<DeferredWorld<'_>> for &'_ [Entity; N] {
    type Output<'w> = [EntityMut<'w>; N];

    unsafe fn get_mut<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainerMut>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityMutableFetchError> {
        <Self as ContainerIndexMut<World>>::get_mut(self, container)
    }
}

impl ContainerIndexMut<DeferredWorld<'_>> for &'_ [Entity] {
    type Output<'w> = Vec<EntityMut<'w>>;

    unsafe fn get_mut<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainerMut>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityMutableFetchError> {
        <Self as ContainerIndexMut<World>>::get_mut(self, container)
    }
}

impl ContainerIndexMut<DeferredWorld<'_>> for &'_ EntityHashSet {
    type Output<'w> = EntityHashMap<EntityMut<'w>>;

    unsafe fn get_mut<'w>(
        self,
        container: <DeferredWorld<'_> as RawContainerMut>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityMutableFetchError> {
        <Self as ContainerIndexMut<World>>::get_mut(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityRef<'_>> for ComponentId {
    type Output<'w> = Ptr<'w>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        // SAFETY: caller ensures that the cell has read access to the component.
        unsafe { container.get_by_id(self) }.ok_or(EntityComponentError::MissingComponent(self))
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityRef<'_>> for [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <&Self as ContainerIndex<EntityRef>>::get(&self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityRef<'_>> for &'_ [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        let mut ptrs = [const { MaybeUninit::uninit() }; N];
        for (ptr, &id) in core::iter::zip(&mut ptrs, self) {
            *ptr = MaybeUninit::new(
                // SAFETY: caller ensures that the cell has read access to the component.
                unsafe { container.get_by_id(id) }
                    .ok_or(EntityComponentError::MissingComponent(id))?,
            );
        }

        // SAFETY: Each ptr was initialized in the loop above.
        let ptrs = ptrs.map(|ptr| unsafe { MaybeUninit::assume_init(ptr) });

        Ok(ptrs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityRef<'_>> for &'_ [ComponentId] {
    type Output<'w> = Vec<Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        let mut ptrs = Vec::with_capacity(self.len());
        for &id in self {
            ptrs.push(
                // SAFETY: caller ensures that the cell has read access to the component.
                unsafe { container.get_by_id(id) }
                    .ok_or(EntityComponentError::MissingComponent(id))?,
            );
        }
        Ok(ptrs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityRef<'_>> for &'_ HashSet<ComponentId> {
    type Output<'w> = HashMap<ComponentId, Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        let mut ptrs = HashMap::with_capacity_and_hasher(self.len(), Default::default());
        for &id in self {
            ptrs.insert(
                id,
                // SAFETY: caller ensures that the cell has read access to the component.
                unsafe { container.get_by_id(id) }
                    .ok_or(EntityComponentError::MissingComponent(id))?,
            );
        }
        Ok(ptrs)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityMut<'_>> for ComponentId {
    type Output<'w> = Ptr<'w>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityMut<'_>> for [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityMut<'_>> for &'_ [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityMut<'_>> for &'_ [ComponentId] {
    type Output<'w> = Vec<Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityMut<'_>> for &'_ HashSet<ComponentId> {
    type Output<'w> = HashMap<ComponentId, Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityWorldMut<'_>> for ComponentId {
    type Output<'w> = Ptr<'w>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityWorldMut<'_>> for [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl<const N: usize> ContainerIndex<EntityWorldMut<'_>> for &'_ [ComponentId; N] {
    type Output<'w> = [Ptr<'w>; N];

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityWorldMut<'_>> for &'_ [ComponentId] {
    type Output<'w> = Vec<Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// SAFETY: No mutable references are returned.
unsafe impl ContainerIndex<EntityWorldMut<'_>> for &'_ HashSet<ComponentId> {
    type Output<'w> = HashMap<ComponentId, Ptr<'w>>;

    unsafe fn get<'w>(
        self,
        container: <EntityRef<'_> as RawContainer>::Raw<'w>,
    ) -> Result<Self::Output<'w>, EntityComponentError> {
        <Self as ContainerIndex<EntityRef>>::get(self, container)
    }
}

// unsafe impl<D: QueryData, F: QueryFilter> EcsCellIndex<Query<'_, '_, D, F>> for Entity {
//     type Output<'w> = ROQueryItem<'w, D>;

//     unsafe fn get<'w>(
//         self,
//         container: <Query<'_, '_, D, F> as RawContainer>::Raw<'w>,
//     ) -> Result<Self::Output<'w>, QueryEntityError<'w>> {
//         <Self as EcsCellIndexMut<Query<'_, '_, D::ReadOnly, F>>>::get_mut(
//             self,
//             container.into_readonly(),
//         )
//     }
// }

// impl<D: QueryData, F: QueryFilter> EcsCellIndexMut<Query<'_, '_, D, F>> for Entity {
//     type Output<'w> = D::Item<'w>;

//     unsafe fn get_mut<'w>(
//         self,
//         container: <Query<'_, '_, D, F> as RawContainerMut>::Raw<'w>,
//     ) -> Result<Self::Output<'w>, QueryEntityError<'w>> {
//         // SAFETY: system runs without conflicts with other systems.
//         // same-system queries have runtime borrow checks when they conflict
//         unsafe {
//             let location =
//                 container
//                     .world
//                     .entities()
//                     .get(self)
//                     .ok_or(EntityDoesNotExistError::new(
//                         self,
//                         container.world.entities(),
//                     ))?;
//             if !container
//                 .state
//                 .matched_archetypes
//                 .contains(location.archetype_id.index())
//             {
//                 return Err(QueryEntityError::QueryDoesNotMatch(self, container.world));
//             }
//             let archetype = container
//                 .world
//                 .archetypes()
//                 .get(location.archetype_id)
//                 .debug_checked_unwrap();
//             let mut fetch = D::init_fetch(
//                 container.world,
//                 &container.state.fetch_state,
//                 container.last_run,
//                 container.this_run,
//             );
//             let mut filter = F::init_fetch(
//                 container.world,
//                 &container.state.filter_state,
//                 container.last_run,
//                 container.this_run,
//             );

//             let table = container
//                 .world
//                 .storages()
//                 .tables
//                 .get(location.table_id)
//                 .debug_checked_unwrap();
//             D::set_archetype(&mut fetch, &container.state.fetch_state, archetype, table);
//             F::set_archetype(&mut filter, &container.state.filter_state, archetype, table);

//             if F::filter_fetch(&mut filter, self, location.table_row) {
//                 Ok(D::fetch(&mut fetch, self, location.table_row))
//             } else {
//                 Err(QueryEntityError::QueryDoesNotMatch(self, container.world))
//             }
//         }
//     }
// }
