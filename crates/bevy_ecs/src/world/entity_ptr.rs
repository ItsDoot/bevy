use core::{
    any::TypeId,
    cmp::Ordering,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use crate::{
    archetype::Archetype,
    bundle::Bundle,
    component::{ComponentId, ComponentTicks, Components, Mutable},
    entity::{Entity, EntityBorrow, EntityLocation, TrustedEntityBorrow},
    prelude::Component,
    query::{Access, ReadOnlyQueryData},
    world::{
        error::EntityComponentError, unsafe_world_cell::UnsafeEntityCell, DynamicComponentFetch,
        Mut, Ref,
    },
};

/// A pointer to an [`Entity`] with access to some or all of its components,
/// as determined by the [`Scope`] `S`. The type of operations available are
/// determined by the [`Capability`] `C`. (i.e. whether the entity is read-only
/// or mutable).
///
/// # Capabilities
///
/// Capabilities describe what you can _do_ to data referenced by an entity
/// pointer. The [`Shared`] capability allows for shared, or "read-only",
/// access. This is analagous to Rust's `&T` reference type. Following from
/// this, the [`Exclusive`] capability allows for exclusive, or "mutable",
/// access. Again, analogous to Rust's `&mut T` reference type.
///
/// # Scopes
///
/// Scopes describe _what_ you can access with an entity pointer. The typical
/// scope for an entity pointer is [`Full`], permitting visibility over all
/// components owned by this entity. [`Global`] is a wider scope, allowing
/// visibility over the entire [`World`] that this entity lives in.
///
/// In the opposite direction, [`Except`], [`Only`], and [`Partial`] give
/// subsets of [`Full`] access:
///
/// - [`Except`] provides access to all components _except_ those given in
///   the [`Bundle`] `B`.
/// - [`Only`] is the inverse of [`Except`], providing access _only_ to a
///   given [`Bundle`] `B`.
/// - [`Partial`] is a more complex subset of [`Full`], where the exact items
///   available are defined at runtime via an [`Access<ComponentId>`].
///
/// # Table of Scopes vs Capabilities
///
/// Scopes are across the top, while Capabilities are along the left-hand side.
///
/// |               | [`Full`]      | [`Global`]     | [`Except`]      | [`Only`]      | Partial           |
/// |---------------|---------------|----------------|-----------------|---------------|-------------------|
/// | [`Shared`]    | [`EntityRef`] | EntityWorldRef | EntityRefExcept | EntityRefOnly | FilteredEntityRef |
/// | [`Exclusive`] | [`EntityMut`] | EntityWorldMut | EntityMutExcept | EntityMutOnly | FilteredEntityMut |
#[derive(Clone, Copy)]
pub struct EntityPtr<'w, S: Scope, C: Capability> {
    pub(crate) cell: UnsafeEntityCell<'w>,
    scope: S,
    _capability: C,
}

/// Provides read-only access to a particular [`Entity`] and all of its components.
///
/// See [`EntityPtr`] for more information on entity pointers.
/// See [`EntityMut`] for the mutable equivalent.
///
/// # Examples
///
/// Read-only access disjoint with mutable access.
///
/// ```
/// # use bevy_ecs::prelude::*;
/// # #[derive(Component)] pub struct A;
/// # #[derive(Component)] pub struct B;
/// fn disjoint_system(
///     query1: Query<&mut A>,
///     query2: Query<EntityRef, Without<A>>,
/// ) {
///     // ...
/// }
/// # bevy_ecs::system::assert_is_system(disjoint_system);
/// ```
pub type EntityRef<'w> = EntityPtr<'w, Full, Shared>;

/// Provides mutable access to a particular [`Entity`] and all of its components.
///
/// See [`EntityPtr`] for more information on entity pointers.
/// See [`EntityRef`] for the read-only equivalent.
/// See [`EntityWorldMut`] for the ability to add/remove components, despawning
/// the entity, and full mutable access to the entire world.
///
/// # Examples
///
/// Disjoint mutable access.
///
/// ```
/// # use bevy_ecs::prelude::*;
/// # #[derive(Component)] pub struct A;
/// fn disjoint_system(
///     query1: Query<EntityMut, With<A>>,
///     query2: Query<EntityMut, Without<A>>,
/// ) {
///     // ...
/// }
/// # bevy_ecs::system::assert_is_system(disjoint_system);
/// ```
pub type EntityMut<'w> = EntityPtr<'w, Full, Exclusive>;

impl<'w, S: Scope, C: Capability> EntityPtr<'w, S, C> {
    /// # Safety
    ///
    /// The caller must ensure that:
    /// - The `cell` must be permitted to be used with the given `scope` without
    ///   violating Rust's aliasing rules.
    /// - For a `capability` of [`Shared`], no mutable accesses are made to any
    ///   of the entity's scoped components while this entity pointer is alive.
    /// - For a `capability` of [`Exclusive`], no other entity pointers are
    ///   alive that have access to the same entity's scoped components.
    ///
    /// For example, having two entity pointers to the same entity with at least
    /// one being [`Exclusive`] requires that neither are allowed access to any
    /// of the same components (i.e. no overlapping [`Scope`]s).
    pub(crate) unsafe fn new(cell: UnsafeEntityCell<'w>, scope: S, capability: C) -> Self {
        Self {
            cell,
            scope,
            _capability: capability,
        }
    }

    /// Returns a read-only entity pointer to the current entity.
    pub fn as_readonly(&self) -> EntityPtr<'_, S::AsRef<'_>, Shared> {
        // SAFETY: Taking `&self` and downgrading the capability from
        // maybe-exclusive to shared ensures that no mutable references to the
        // entity's components exist at this point within this scope.
        unsafe { EntityPtr::new(self.cell, self.scope.as_ref(), Shared) }
    }

    /// Consumes the entity pointer and returns a read-only entity pointer to
    /// the current entity.
    pub fn into_readonly(self) -> EntityPtr<'w, S, Shared> {
        // SAFETY: Consuming `self` and downgrading the capability from
        // maybe-exclusive to shared ensures that no mutable references to the
        // entity's components exist at this point within this scope.
        unsafe { EntityPtr::new(self.cell, self.scope, Shared) }
    }

    /// Returns a reference to the [`Scope`] of the current entity pointer.
    pub fn scope(&self) -> &S {
        &self.scope
    }

    /// Consumes the entity pointer and returns the [`Scope`] of the current
    /// entity pointer.
    pub fn into_scope(self) -> S {
        self.scope
    }

    /// Returns the [ID](Entity) of the current entity.
    #[inline]
    #[must_use = "Omit the .id() call if you do not need to store the `Entity` identifier."]
    pub fn id(&self) -> Entity {
        self.cell.id()
    }

    /// Gets metadata indicating the location where the current entity is stored.
    #[inline]
    pub fn location(&self) -> EntityLocation {
        self.cell.location()
    }

    /// Returns the archetype that the current entity belongs to.
    #[inline]
    pub fn archetype(&self) -> &Archetype {
        self.cell.archetype()
    }

    /// Returns `true` if the current entity has a component of type `T`.
    /// Otherwise, this returns `false`.
    ///
    /// ## Notes
    ///
    /// If you do not know the concrete type of a component, consider using
    /// [`Self::contains_id`] or [`Self::contains_type_id`].
    #[inline]
    pub fn contains<T: Component>(&self) -> bool {
        self.contains_type_id(TypeId::of::<T>())
    }

    /// Returns `true` if the current entity has a component identified by
    /// `component_id`. Otherwise, this returns false.
    ///
    /// ## Notes
    ///
    /// - If you know the concrete type of the component, you should prefer
    ///   [`Self::contains`].
    /// - If you know the component's [`TypeId`] but not its [`ComponentId`],
    ///   consider using [`Self::contains_type_id`].
    #[inline]
    pub fn contains_id(&self, component_id: ComponentId) -> bool {
        self.cell.contains_id(component_id)
    }

    /// Returns `true` if the current entity has a component with the type
    /// identified by `type_id`. Otherwise, this returns false.
    ///
    /// ## Notes
    ///
    /// - If you know the concrete type of the component, you should prefer
    ///   [`Self::contains`].
    /// - If you have a [`ComponentId`] instead of a [`TypeId`], consider using
    ///   [`Self::contains_id`].
    #[inline]
    pub fn contains_type_id(&self, type_id: TypeId) -> bool {
        self.cell.contains_type_id(type_id)
    }

    /// Retrieves the change ticks for the given component. This can be useful
    /// for implementing change detection in custom runtimes.
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow read access to the component.
    #[inline]
    pub fn get_change_ticks<T: Component>(&self) -> Option<ComponentTicks> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_change_ticks::<T>(&self.scope) }
    }

    /// Retrieves the change ticks for the given [`ComponentId`]. This can be
    /// useful for implementing change detection in custom runtimes.
    ///
    /// **You should prefer to use the typed API [`EntityRef::get_change_ticks`]
    /// where possible and only use this in cases where the actual component
    /// types are not known at compile time.**
    ///
    /// Returns `None` if the entity does not have a component with the given ID
    /// or if the [`Scope`] `S` does not allow read access to the component.
    #[inline]
    pub fn get_change_ticks_by_id(&self, component_id: ComponentId) -> Option<ComponentTicks> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_change_ticks_by_id(&self.scope, component_id) }
    }

    /// Gets access to the component of type `T` for the current entity.
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow read access to the component.
    #[inline]
    pub fn get<T: Component>(&self) -> Option<&'_ T> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get::<T>(&self.scope) }
    }

    /// Gets access to the component of type `T` for the current entity,
    /// including change detection information as a [`Ref`].
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow read access to the component.
    #[inline]
    pub fn get_ref<T: Component>(&self) -> Option<Ref<'_, T>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_ref::<T>(&self.scope) }
    }

    /// Returns [untyped read-only reference(s)](Ptr) to component(s) for the
    /// current entity, based on the given [`ComponentId`]s.
    ///
    /// **You should prefer to use the typed API [`EntityRef::get`] where
    /// possible and only use this in cases where the actual component types
    /// are not known at compile time.**
    ///
    /// Unlike [`EntityRef::get`], this returns untyped reference(s) to
    /// component(s), and it's the job of the caller to ensure the correct
    /// type(s) are dereferenced (if necessary).
    ///
    /// # Errors
    ///
    /// Returns [`EntityComponentError::MissingComponent`] if the entity does
    /// not have a component or the [`Scope`] `S` does not allow read access to
    /// the component.
    ///
    /// # Examples
    ///
    /// ## Single [`ComponentId`]
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Foo(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn(Foo(42)).id();
    ///
    /// // Grab the component ID for `Foo` in whatever way you like.
    /// let component_id = world.register_component::<Foo>();
    ///
    /// // Then, get the component by ID.
    /// let ptr = world.entity(entity).get_by_id(component_id);
    /// # assert_eq!(unsafe { ptr.unwrap().deref::<Foo>() }, &Foo(42));
    /// ```
    ///
    /// ## Array of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a same-sized array.
    /// let Ok([x_ptr, y_ptr]) = world.entity(entity).get_by_id([x_id, y_id]) else {
    ///     // Up to you to handle if a component is missing from the entity.
    /// #   unreachable!();
    /// };
    /// # assert_eq!((unsafe { x_ptr.deref::<X>() }, unsafe { y_ptr.deref::<Y>() }), (&X(42), &Y(10)));
    /// ```
    ///
    /// ## Slice of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_ecs::{prelude::*, component::ComponentId};
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a vec of ptrs.
    /// let ptrs = world.entity(entity).get_by_id(&[x_id, y_id] as &[ComponentId]);
    /// # let ptrs = ptrs.unwrap();
    /// # assert_eq!((unsafe { ptrs[0].deref::<X>() }, unsafe { ptrs[1].deref::<Y>() }), (&X(42), &Y(10)));
    /// ```
    ///
    /// ## [`HashSet`] of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_utils::HashSet;
    /// # use bevy_ecs::{prelude::*, component::ComponentId};
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a vec of ptrs.
    /// let ptrs = world.entity(entity).get_by_id(&HashSet::from_iter([x_id, y_id]));
    /// # let ptrs = ptrs.unwrap();
    /// # assert_eq!((unsafe { ptrs[&x_id].deref::<X>() }, unsafe { ptrs[&y_id].deref::<Y>() }), (&X(42), &Y(10)));
    /// ```
    #[inline]
    pub fn get_by_id<F: DynamicComponentFetch>(
        &self,
        component_ids: F,
    ) -> Result<F::Ref<'_>, EntityComponentError> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { component_ids.fetch_ref(&self.scope, self.cell) }
    }

    /// Returns read-only components for the current entity that match the query `Q`.
    ///
    /// # Panics
    ///
    /// If the entity does not have the components required by the query `Q`, or
    /// if the [`Scope`] `S` does not allow read access to any of the components.
    pub fn components<Q: ReadOnlyQueryData>(&self) -> Q::Item<'_> {
        self.get_components::<Q>().expect(QUERY_MISMATCH_ERROR)
    }

    /// Returns read-only components for the current entity that match the query `Q`.
    ///
    /// Returns `None` if the entity does not have the components required by
    /// the query `Q`, or if the [`Scope`] `S` does not allow read access to any
    /// of the components.
    pub fn get_components<Q: ReadOnlyQueryData>(&self) -> Option<Q::Item<'_>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_components::<Q>(&self.scope) }
    }

    /// Consumes `self` and gets access to the component of type `T` with the
    /// world `'w` lifetime for the current entity.
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow read access to the component.
    pub fn into_borrow<T: Component>(self) -> Option<&'w T> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get::<T>(&self.scope) }
    }

    /// Consumes `self` and gets access to the component of type `T` with world
    /// `'w` lifetime for the current entity, including change detection information
    /// as a [`Ref<'w>`].
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow read access to the component.
    pub fn into_ref<T: Component>(self) -> Option<Ref<'w, T>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_ref::<T>(&self.scope) }
    }

    /// Consumes `self` and returns [untyped read-only reference(s)](Ptr) to
    /// component(s) with lifetime `'w` for the current entity, based on the
    /// given [`ComponentId`]s.
    ///
    /// **You should prefer to use the typed API [`EntityPtr::into_borrow`]
    /// where possible and only use this in cases where the actual component
    /// types are not known at compile time.**
    ///
    /// Unlike [`EntityPtr::into_borrow`], this returns untyped reference(s) to
    /// component(s), and it's the job of the caller to ensure the correct
    /// type(s) are dereferenced (if necessary).
    ///
    /// # Errors
    ///
    /// Returns [`EntityComponentError::MissingComponent`] if the entity does
    /// not have a component or the [`Scope`] `S` does not allow read access to
    /// the component.
    ///
    /// # Examples
    ///
    /// For examples on how to use this method, see [`EntityPtr::get_by_id`].
    pub fn into_borrow_by_id<F: DynamicComponentFetch>(
        self,
        component_ids: F,
    ) -> Result<F::Ref<'w>, EntityComponentError> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { component_ids.fetch_ref(&self.scope, self.cell) }
    }

    /// Consumes `self` and returns read-only components with the world `'w`
    /// lifetime for the current entity that match the query `Q`.
    ///
    /// # Panics
    ///
    /// If the entity does not have the components required by the query `Q`, or
    /// if the [`Scope`] `S` does not allow read access to any of the components.
    pub fn into_components<Q: ReadOnlyQueryData>(self) -> Q::Item<'w> {
        self.try_into_components::<Q>().expect(QUERY_MISMATCH_ERROR)
    }

    /// Consumes `self` and returns read-only components with the world `'w`
    /// lifetime for the current entity that match the query `Q`,
    ///
    /// Returns `None` if the entity does not have the components required by
    /// the query `Q`, or if the [`Scope`] `S` does not allow read access to any
    /// of the components.
    pub fn try_into_components<Q: ReadOnlyQueryData>(self) -> Option<Q::Item<'w>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&self` guarantees that no mutable references to the component exist.
        unsafe { self.cell.get_components::<Q>(&self.scope) }
    }

    /// Returns the source code location from which this entity has been spawned.
    #[cfg(feature = "track_change_detection")]
    pub fn spawned_by(&self) -> &'static core::panic::Location<'static> {
        self.cell.spawned_by()
    }
}

/// Operations only available with mutable access to the entity's components.
impl<'w, S: Scope> EntityPtr<'w, S, Exclusive> {
    /// Returns a new instance with a shorter lifetime.
    /// This is useful if you have `&mut EntityPtr`, but you need `EntityPtr`.
    pub fn reborrow(&mut self) -> EntityPtr<'_, S::AsRef<'_>, Exclusive> {
        // SAFETY: Neither the scope nor the capability are changed, only the
        // lifetime is shortened. Therefore no aliasing rules are violated.
        unsafe { EntityPtr::new(self.cell, self.scope.as_ref(), Exclusive) }
    }

    /// Gets mutable access to the component of type `T` for the current entity.
    ///
    /// Returns `None` if the entity does not have a component of type `T`
    /// or if the [`Scope`] `S` does not allow write access to the component.
    pub fn get_mut<T: Component<Mutability = Mutable>>(&mut self) -> Option<Mut<'_, T>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&mut self` guarantees that no other references to the component exist.
        unsafe { self.cell.get_mut::<T>(&self.scope) }
    }

    /// Gets mutable access to the component of type `T` for the current entity.
    ///
    /// Returns `None` if the entity does not have a component of type `T` or if
    /// the [`Scope`] `S` does not allow write access to the component.
    ///
    /// # Safety
    ///
    /// - `T` must be a mutable component
    #[inline]
    pub unsafe fn get_mut_assume_mutable<T: Component>(&mut self) -> Option<Mut<'_, T>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&mut self` guarantees that no other references to the component exist.
        // - The caller ensures that `T` is a mutable component.
        unsafe { self.cell.get_mut_assume_mutable::<T>(&self.scope) }
    }

    /// Returns [untyped mutable reference(s)](MutUntyped) to component(s) for
    /// the current entity, based on the given [`ComponentId`]s.
    ///
    /// **You should prefer to use the typed API [`EntityPtr::get_mut`] where
    /// possible and only use this in cases where the actual component types
    /// are not known at compile time.**
    ///
    /// Unlike [`EntityPtr::get_mut`], this returns untyped reference(s) to
    /// component(s), and it's the job of the caller to ensure the correct
    /// type(s) are dereferenced (if necessary).
    ///
    /// # Errors
    ///
    /// - Returns [`EntityComponentError::MissingComponent`] if the entity does
    ///   not have a component or the [`Scope`] `S` does not allow write access
    ///   to the component.
    /// - Returns [`EntityComponentError::AliasedMutability`] if a component
    ///   is requested multiple times.
    ///
    /// # Examples
    ///
    /// ## Single [`ComponentId`]
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Foo(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn(Foo(42)).id();
    ///
    /// // Grab the component ID for `Foo` in whatever way you like.
    /// let component_id = world.register_component::<Foo>();
    ///
    /// // Then, get the component by ID.
    /// let mut entity_mut = world.entity_mut(entity);
    /// let mut ptr = entity_mut.get_mut_by_id(component_id)
    /// #   .unwrap();
    /// # assert_eq!(unsafe { ptr.as_mut().deref_mut::<Foo>() }, &mut Foo(42));
    /// ```
    ///
    /// ## Array of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_ecs::prelude::*;
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a same-sized array.
    /// let mut entity_mut = world.entity_mut(entity);
    /// let Ok([mut x_ptr, mut y_ptr]) = entity_mut.get_mut_by_id([x_id, y_id]) else {
    ///     // Up to you to handle if a component is missing from the entity.
    /// #   unreachable!();
    /// };
    /// # assert_eq!((unsafe { x_ptr.as_mut().deref_mut::<X>() }, unsafe { y_ptr.as_mut().deref_mut::<Y>() }), (&mut X(42), &mut Y(10)));
    /// ```
    ///
    /// ## Slice of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_ecs::{prelude::*, component::ComponentId, change_detection::MutUntyped};
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a vec of ptrs.
    /// let mut entity_mut = world.entity_mut(entity);
    /// let ptrs = entity_mut.get_mut_by_id(&[x_id, y_id] as &[ComponentId])
    /// #   .unwrap();
    /// # let [mut x_ptr, mut y_ptr]: [MutUntyped; 2] = ptrs.try_into().unwrap();
    /// # assert_eq!((unsafe { x_ptr.as_mut().deref_mut::<X>() }, unsafe { y_ptr.as_mut().deref_mut::<Y>() }), (&mut X(42), &mut Y(10)));
    /// ```
    ///
    /// ## [`HashSet`] of [`ComponentId`]s
    ///
    /// ```
    /// # use bevy_utils::HashSet;
    /// # use bevy_ecs::{prelude::*, component::ComponentId};
    /// #
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct X(i32);
    /// # #[derive(Component, PartialEq, Debug)]
    /// # pub struct Y(i32);
    /// # let mut world = World::new();
    /// let entity = world.spawn((X(42), Y(10))).id();
    ///
    /// // Grab the component IDs for `X` and `Y` in whatever way you like.
    /// let x_id = world.register_component::<X>();
    /// let y_id = world.register_component::<Y>();
    ///
    /// // Then, get the components by ID. You'll receive a `HashMap` of ptrs.
    /// let mut entity_mut = world.entity_mut(entity);
    /// let mut ptrs = entity_mut.get_mut_by_id(&HashSet::from_iter([x_id, y_id]))
    /// #   .unwrap();
    /// # let [Some(mut x_ptr), Some(mut y_ptr)] = ptrs.get_many_mut([&x_id, &y_id]) else { unreachable!() };
    /// # assert_eq!((unsafe { x_ptr.as_mut().deref_mut::<X>() }, unsafe { y_ptr.as_mut().deref_mut::<Y>() }), (&mut X(42), &mut Y(10)));
    /// ```
    pub fn get_mut_by_id<F: DynamicComponentFetch>(
        &mut self,
        component_ids: F,
    ) -> Result<F::Mut<'_>, EntityComponentError> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - `&mut self` guarantees that no other references to the component exist.
        unsafe { component_ids.fetch_mut(&self.scope, self.cell) }
    }

    /// Returns [untyped mutable reference](MutUntyped) to component for
    /// the current entity, based on the given [`ComponentId`].
    ///
    /// Unlike [`EntityMut::get_mut_by_id`], this method borrows &self instead of
    /// &mut self, allowing the caller to access multiple components simultaneously.
    ///
    /// # Errors
    ///
    /// - Returns [`EntityComponentError::MissingComponent`] if the entity does
    ///   not have a component.
    /// - Returns [`EntityComponentError::AliasedMutability`] if a component
    ///   is requested multiple times.
    ///
    /// # Safety
    ///
    /// It is the callers responsibility to ensure that
    /// - the [`UnsafeEntityCell`] has permission to access the component mutably
    /// - no other references to the component exist at the same time
    #[inline]
    pub unsafe fn get_mut_by_id_unchecked<F: DynamicComponentFetch>(
        &self,
        component_ids: F,
    ) -> Result<F::Mut<'_>, EntityComponentError> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - The caller ensures that no other references to the fetched components
        //   exist at the same time.
        unsafe { component_ids.fetch_mut(&self.scope, self.cell) }
    }

    /// Consumes self and gets mutable access to the component of type `T`
    /// with the world `'w` lifetime for the current entity.
    ///
    /// Returns `None` if the entity does not have a component of type `T`
    /// or if the [`Scope`] `S` does not allow write access to the component.
    pub fn into_mut<T: Component<Mutability = Mutable>>(self) -> Option<Mut<'w, T>> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - Consuming `self` ensures that no other references exist to this entity's components.
        unsafe { self.cell.get_mut::<T>(&self.scope) }
    }

    /// Consumes `self` and returns [untyped mutable reference(s)](MutUntyped)
    /// to component(s) with lifetime `'w` for the current entity, based on the
    /// given [`ComponentId`]s.
    ///
    /// **You should prefer to use the typed API [`EntityPtr::into_mut`] where
    /// possible and only use this in cases where the actual component types
    /// are not known at compile time.**
    ///
    /// Unlike [`EntityPtr::into_mut`], this returns untyped reference(s) to
    /// component(s), and it's the job of the caller to ensure the correct
    /// type(s) are dereferenced (if necessary).
    ///
    /// # Errors
    ///
    /// - Returns [`EntityComponentError::MissingComponent`] if the entity does
    ///   not have a component or the [`Scope`] `S` does not allow write access
    ///   to the component.
    /// - Returns [`EntityComponentError::AliasedMutability`] if a component
    ///   is requested multiple times.
    ///
    /// # Examples
    ///
    /// For examples on how to use this method, see [`EntityPtr::get_mut_by_id`].
    pub fn into_mut_by_id<F: DynamicComponentFetch>(
        self,
        component_ids: F,
    ) -> Result<F::Mut<'w>, EntityComponentError> {
        // SAFETY:
        // - The scope provided was constructed with this entity pointer.
        // - Consuming `self` ensures that no other references exist to this entity's components.
        unsafe { component_ids.fetch_mut(&self.scope, self.cell) }
    }
}

impl<S: Scope, C: Capability> PartialEq for EntityPtr<'_, S, C> {
    fn eq(&self, other: &Self) -> bool {
        self.entity() == other.entity()
    }
}

impl<S: Scope, C: Capability> Eq for EntityPtr<'_, S, C> {}

impl<S: Scope, C: Capability> PartialOrd for EntityPtr<'_, S, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<S: Scope, C: Capability> Ord for EntityPtr<'_, S, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.entity().cmp(&other.entity())
    }
}

impl<S: Scope, C: Capability> Hash for EntityPtr<'_, S, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.entity().hash(state);
    }
}

impl<S: Scope, C: Capability> EntityBorrow for EntityPtr<'_, S, C> {
    fn entity(&self) -> Entity {
        self.id()
    }
}

// SAFETY: This type represents one Entity. We implement the comparison traits based on that Entity.
unsafe impl<S: Scope, C: Capability> TrustedEntityBorrow for EntityPtr<'_, S, C> {}

impl<'w, S: Scope> From<EntityPtr<'w, S, Exclusive>> for EntityPtr<'w, S, Shared> {
    fn from(value: EntityPtr<'w, S, Exclusive>) -> Self {
        value.into_readonly()
    }
}

impl<'a, S: Scope, C: Capability> From<&'a EntityPtr<'_, S, C>>
    for EntityPtr<'a, S::AsRef<'a>, Shared>
{
    fn from(value: &'a EntityPtr<'_, S, C>) -> Self {
        value.as_readonly()
    }
}

impl<'a, S: Scope> From<&'a mut EntityPtr<'_, S, Exclusive>>
    for EntityPtr<'a, S::AsRef<'a>, Exclusive>
{
    fn from(value: &'a mut EntityPtr<'_, S, Exclusive>) -> Self {
        value.reborrow()
    }
}

const QUERY_MISMATCH_ERROR: &str = "Query does not match the current entity";

/// Scopes define which components are accessible by an entity pointer.
///
/// See [`EntityPtr`] for more information, specifically the "Scopes" section.
pub trait Scope: sealed::Scope {
    /// Associated type for taking this scope by reference.
    type AsRef<'a>: Scope
    where
        Self: 'a;

    /// Returns a reference to the current scope.
    fn as_ref(&self) -> Self::AsRef<'_>;

    /// Returns `true` if the current scope allows read access to the component.
    fn can_read(&self, components: &Components, component: ComponentId) -> bool;

    /// Returns `true` if the current scope allows write access to the component.
    fn can_write(&self, components: &Components, component: ComponentId) -> bool;
}

impl<S: Scope> Scope for &S {
    type AsRef<'a>
        = Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        *self
    }

    #[inline(always)]
    fn can_read(&self, components: &Components, component: ComponentId) -> bool {
        (*self).can_read(components, component)
    }

    #[inline(always)]
    fn can_write(&self, components: &Components, component: ComponentId) -> bool {
        (*self).can_write(components, component)
    }
}

/// [`EntityPtr`] [`Scope`] that provides full access to the entity's components.
///
/// See [`EntityRef`] and [`EntityMut`] which operate in this scope.
#[derive(Clone, Copy)]
pub struct Full;

impl Scope for Full {
    type AsRef<'a>
        = Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        *self
    }

    #[inline(always)]
    fn can_read(&self, _components: &Components, _component: ComponentId) -> bool {
        true
    }

    #[inline(always)]
    fn can_write(&self, _components: &Components, _component: ComponentId) -> bool {
        true
    }
}

/// [`EntityPtr`] [`Scope`] that provides full access to the entity's components
/// and the [`World`] that the entity is contained in.
///
/// See [`EntityWorldRef`] and [`EntityWorldMut`] which operate in this scope.
#[derive(Clone, Copy)]
pub struct Global;

impl Scope for Global {
    type AsRef<'a>
        = Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        *self
    }

    #[inline(always)]
    fn can_read(&self, _components: &Components, _component: ComponentId) -> bool {
        true
    }

    #[inline(always)]
    fn can_write(&self, _components: &Components, _component: ComponentId) -> bool {
        true
    }
}

/// [`EntityPtr`] [`Scope`] that provides access to all components *except*
/// those in the [`Bundle`] `B`.
///
/// See [`EntityRefExcept`] and [`EntityMutExcept`] which operate in this scope.
pub struct Except<B: Bundle>(PhantomData<B>);

impl<B: Bundle> Clone for Except<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Bundle> Copy for Except<B> {}

impl<B: Bundle> Default for Except<B> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<B: Bundle> Scope for Except<B> {
    type AsRef<'a>
        = Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        *self
    }

    fn can_read(&self, components: &Components, component: ComponentId) -> bool {
        let mut found = false;
        B::get_component_ids(components, &mut |maybe_id| {
            if let Some(id) = maybe_id {
                found = found || id == component;
            }
        });
        !found
    }

    fn can_write(&self, components: &Components, component: ComponentId) -> bool {
        let mut found = false;
        B::get_component_ids(components, &mut |maybe_id| {
            if let Some(id) = maybe_id {
                found = found || id == component;
            }
        });
        !found
    }
}

/// [`EntityPtr`] [`Scope`] that provides access to *only* the components which
/// are included in the [`Bundle`] `B`.
///
/// See [`EntityRefOnly`] and [`EntityMutOnly`] which operate in this scope.
pub struct Only<B: Bundle>(PhantomData<B>);

impl<B: Bundle> Clone for Only<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Bundle> Copy for Only<B> {}

impl<B: Bundle> Default for Only<B> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<B: Bundle> Scope for Only<B> {
    type AsRef<'a>
        = Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        *self
    }

    fn can_read(&self, components: &Components, component: ComponentId) -> bool {
        let mut found = false;
        B::get_component_ids(components, &mut |maybe_id| {
            if let Some(id) = maybe_id {
                found = found || id == component;
            }
        });
        found
    }

    fn can_write(&self, components: &Components, component: ComponentId) -> bool {
        let mut found = false;
        B::get_component_ids(components, &mut |maybe_id| {
            if let Some(id) = maybe_id {
                found = found || id == component;
            }
        });
        found
    }
}

impl Scope for Access<ComponentId> {
    type AsRef<'a>
        = &'a Self
    where
        Self: 'a;

    fn as_ref(&self) -> Self::AsRef<'_> {
        self
    }

    fn can_read(&self, _components: &Components, component: ComponentId) -> bool {
        self.has_component_read(component)
    }

    fn can_write(&self, _components: &Components, component: ComponentId) -> bool {
        self.has_component_write(component)
    }
}

/// Capabilities define what operations are allowed on the data referenced
/// by an entity pointer.
///
/// See [`EntityPtr`] for more information, specifically the "Capabilities" section.
pub trait Capability: sealed::Capability {}

/// [`EntityPtr`] [`Capability`] that allows read-only access to the entity's components.
#[derive(Clone, Copy)]
pub struct Shared;

impl Capability for Shared {}

/// [`EntityPtr`] [`Capability`] that allows mutable access to the entity's components.
pub struct Exclusive;

impl Capability for Exclusive {}

mod sealed {
    pub trait Capability {}
    impl Capability for super::Shared {}
    impl Capability for super::Exclusive {}

    pub trait Scope {}
    impl<S: Scope> Scope for &S {}
    impl Scope for super::Full {}
    impl Scope for super::Global {}
    impl<B: super::Bundle> Scope for super::Except<B> {}
    impl<B: super::Bundle> Scope for super::Only<B> {}
    impl Scope for super::Access<super::ComponentId> {}
}
