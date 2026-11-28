
/// Key-entry duo type.
pub type Take<T> = (String, T);

/// 'Viewable' key-entry duo type.
pub type Sight<'a, T> = (String, &'a T);

/// 'Viewable' mutable key-entry duo type.
pub type SightMut<'a, T> = (String, &'a mut T);

/// Keys extraction type.
pub type Keys = Vec<String>;

/// Values acquisition type.
pub type Values<T> = Vec<T>;

/// 'Scenic' series type.
pub type Collage<T> = Vec<T>;
