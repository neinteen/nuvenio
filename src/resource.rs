//! The resource module contains all the functionality related to resources.
//!
//! Resources are a way to share data between systems,
//! and are used in combination with [`Handler`]s.

use core::ptr::NonNull;

use crate::{map::TypeIdMap, prelude::HandlerParam};

pub use nuvenio_macros::Resource;

/// A wrapper around a [`Resource`].
///
/// This is useful for accessing a [`Resource`] within a handler.
#[derive(Debug)]
// FIXME: resource shouldn't be Option<R> by default.
pub struct Res<'a, R: Resource>(pub(crate) Option<&'a R>);

impl<'a, R: Resource> Res<'a, R> {
    #[allow(dead_code)]
    pub(crate) fn new(r: &'a R) -> Self {
        Self::from(r)
    }
}

impl<'a, R: Resource> From<&'a R> for Res<'a, R> {
    fn from(value: &'a R) -> Self {
        Self(Some(value))
    }
}

impl<'a, R: Resource + core::ops::Deref> core::ops::Deref for Res<'a, R> {
    type Target = Option<&'a R>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

unsafe impl<T: Resource> HandlerParam for Res<'_, T> {
    type State = ();

    type This<'a> = Res<'a, T>;

    fn init(
        _: &mut crate::prelude::World,
        _: &mut crate::handler::HandlerConfig,
    ) -> Result<Self::State, crate::handler::InitError> {
        Ok(())
    }

    unsafe fn get<'a>(
        (): &'a mut Self::State,
        _: &'a crate::handler::HandlerInfo,
        _: crate::event::EventPtr<'a>,
        _: crate::entity::EntityLocation,
        world: crate::world::UnsafeWorldCell<'a>,
    ) -> Self::This<'a> {
        Res(world.world_mut().get_resource())
    }

    fn refresh_archetype((): &mut Self::State, _: &crate::archetype::Archetype) {}

    fn remove_archetype((): &mut Self::State, _: &crate::archetype::Archetype) {}
}

/// A mutable wrapper around a [`Resource`].
///
/// This is useful for accessing a [`Resource`] within a handler.
#[derive(Debug)]
// FIXME: implement &'a R with panic when resource doesn't exist.
pub struct ResMut<'a, R: Resource>(pub(crate) Option<&'a mut R>);

impl<'a, R: Resource> ResMut<'a, R> {
    #[allow(dead_code)]
    pub(crate) fn new(r: &'a mut R) -> Self {
        Self::from(r)
    }
}

impl<'a, R: Resource> From<&'a mut R> for ResMut<'a, R> {
    fn from(value: &'a mut R) -> Self {
        Self(Some(value))
    }
}

impl<'a, R: Resource + core::ops::Deref> core::ops::Deref for ResMut<'a, R> {
    type Target = Option<&'a mut R>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

unsafe impl<T: Resource> HandlerParam for ResMut<'_, T> {
    type State = ();

    type This<'a> = ResMut<'a, T>;

    fn init(
        _: &mut crate::prelude::World,
        _: &mut crate::handler::HandlerConfig,
    ) -> Result<Self::State, crate::handler::InitError> {
        Ok(())
    }

    unsafe fn get<'a>(
        (): &'a mut Self::State,
        _: &'a crate::handler::HandlerInfo,
        _: crate::event::EventPtr<'a>,
        _: crate::entity::EntityLocation,
        world: crate::world::UnsafeWorldCell<'a>,
    ) -> Self::This<'a> {
        ResMut(world.world_mut().get_resource_mut())
    }

    fn refresh_archetype(_state: &mut Self::State, _arch: &crate::archetype::Archetype) {}

    fn remove_archetype(_state: &mut Self::State, _arch: &crate::archetype::Archetype) {}
}

/// A marker trait for [`Resource`]s.
///
/// Resources are data that can be shared between multiple [`Handler`]s.
pub trait Resource: 'static {}

/// Stores [`Resource`]s in the World.
///
/// Resources are data that can be shared between multiple [`Handler`]s.
///
/// By adding `&Resources` or `&mut Resources` to your handler, you can access all [`Resource`]s in the world.
///
/// To access a resource directly, you can use the Res<T> or `ResMut`<T> wrapper.
#[derive(Debug)]
pub struct Resources {
    by_id: TypeIdMap<NonNull<dyn Resource>>,
}
impl Resources {
    pub(crate) fn new() -> Self {
        Self {
            by_id: TypeIdMap::default(),
        }
    }

    /// Adds a [`Resource`] to the collection.
    ///
    /// Returns the previous [`Resource`] if it existed.
    ///
    /// # Examples
    ///
    /// ```
    /// use nuvenio::prelude::*;
    ///
    /// #[derive(Resource, Debug, PartialEq)]
    /// struct MyResource(i32);
    ///
    /// let mut world = World::new();
    ///
    /// world.add_resource(MyResource(42));
    /// ```
    pub fn add<R: Resource>(&mut self, res: R) -> Option<R> {
        self.by_id
            .insert(
                core::any::TypeId::of::<R>(),
                NonNull::new(Box::into_raw(Box::new(res)) as *mut dyn Resource).unwrap(),
            )
            // SAFETY: pointer is not null, valid, guaranteed to be a Resource, and there can only be one of each type.
            .map(|r| *unsafe { Box::from_raw(r.as_ptr() as *mut R) })
    }

    /// Retrieves a [`Resource`] from the collection.
    ///
    /// Returns `None` if the [`Resource`] does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use nuvenio::prelude::*;
    ///
    /// #[derive(Resource, Debug, PartialEq)]
    /// struct MyResource(i32);
    ///
    /// let mut world = World::new();
    ///
    /// world.add_resource(MyResource(42));
    ///
    /// assert_eq!(world.get_resource::<MyResource>(), Some(&MyResource(42)));
    /// ```
    pub fn get<R: Resource>(&self) -> Option<&R> {
        self.by_id
            .get(&core::any::TypeId::of::<R>())
            // SAFETY: pointer is not null, valid, guaranteed to be a Resource, and there can only be one of each type.
            .map(|r| unsafe { r.cast::<R>().as_ref() })
    }

    /// Retrieves a mutable [`Resource`] from the collection.
    ///
    /// Returns `None` if the [`Resource`] does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use nuvenio::prelude::*;
    ///
    /// #[derive(Resource, Debug, PartialEq)]
    /// struct MyResource(i32);
    ///
    /// let mut world = World::new();
    ///
    /// world.add_resource(MyResource(42));
    ///
    /// {
    ///     let mut resource = world.get_resource_mut::<MyResource>().unwrap();
    ///     resource.0 += 1;
    /// }
    ///
    /// assert_eq!(world.get_resource_mut::<MyResource>(), Some(&mut MyResource(43)));
    /// ```
    pub fn get_mut<R: Resource>(&mut self) -> Option<&mut R> {
        self.by_id
            .get_mut(&core::any::TypeId::of::<R>())
            // SAFETY: pointer is not null, valid, guaranteed to be a Resource, and there can only be one of each type.
            .map(|r| unsafe { &mut *(r.as_ptr() as *mut R) })
    }

    /// Removes a [`Resource`] from the collection.
    ///
    /// Returns the [`Resource`] if it existed.
    ///
    /// # Examples
    ///
    /// ```
    /// use nuvenio::prelude::*;
    ///
    /// #[derive(Resource, Debug, PartialEq)]
    /// struct MyResource(i32);
    ///
    /// let mut world = World::new();
    ///
    /// world.add_resource(MyResource(42));
    ///
    /// assert_eq!(world.remove_resource::<MyResource>(), Some(MyResource(42)));
    /// ```
    pub fn remove<R: Resource>(&mut self) -> Option<R> {
        self.by_id
            .remove(&core::any::TypeId::of::<R>())
            // SAFETY: pointer is not null, valid, guaranteed to be a Resource, and there can only be one of each type.
            .map(|r| *unsafe { Box::from_raw(r.as_ptr() as *mut R) })
    }
}

unsafe impl HandlerParam for &'_ Resources {
    type State = ();

    type This<'a> = &'a Resources;

    fn init(
        _: &mut crate::prelude::World,
        _: &mut crate::handler::HandlerConfig,
    ) -> Result<Self::State, crate::handler::InitError> {
        Ok(())
    }

    unsafe fn get<'a>(
        (): &'a mut Self::State,
        _: &'a crate::handler::HandlerInfo,
        _: crate::event::EventPtr<'a>,
        _: crate::entity::EntityLocation,
        world: crate::world::UnsafeWorldCell<'a>,
    ) -> Self::This<'a> {
        world.resources()
    }

    fn refresh_archetype((): &mut Self::State, _: &crate::archetype::Archetype) {}

    fn remove_archetype((): &mut Self::State, _: &crate::archetype::Archetype) {}
}

#[cfg(test)]
mod tests {
    use nuvenio_macros::GlobalEvent;

    use crate::{event::Receiver, prelude::World};

    use super::*;

    #[derive(GlobalEvent, Debug)]
    struct Tick;
    #[derive(Resource, Debug, PartialEq)]
    struct MyResource(i32);

    #[test]
    fn resource() {
        let mut world = World::new();
        world.add_resource(MyResource(42));

        world.add_handler(|_: Receiver<Tick>, res: Res<MyResource>| {
            let res = res.0.unwrap();
            assert_eq!(res, &MyResource(42));
        });

        world.send(Tick)
    }

    #[test]
    fn resource_mut() {
        let mut world = World::new();
        world.add_resource(MyResource(42));

        world.add_handler(|_: Receiver<Tick>, res: ResMut<MyResource>| {
            let res = res.0.unwrap();
            res.0 += 1;
        });

        for _ in 0..10 {
            world.send(Tick)
        }

        assert_eq!(world.get_resource::<MyResource>().unwrap(), &MyResource(52));
    }
}
