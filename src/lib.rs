//! # serde-aux
//!
//! A serde auxiliary library.

#![deny(missing_docs)]
#![deny(warnings)]

#[macro_use] extern crate serde;

/// Contains helpers for the containers.
pub mod container_attributes;
/// Contains helpers for the fields.
pub mod field_attributes;
/// Contains helpers to get serialization names for struct fields and enum variants as they are serialized.
pub mod serde_introspection;

/// Prelude module, contains the most needed helpers from this library.
pub mod prelude {
    pub use crate::container_attributes::*;
    pub use crate::field_attributes::*;
    pub use crate::serde_introspection::*;
}
