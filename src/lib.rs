//! # serde-aux
//!
//! A serde auxiliary library.

#![deny(missing_docs)]
#![deny(warnings)]

/// Contains helpers for the containers.
pub mod container_attributes;
/// Contains helpers for the fields.
pub mod field_attributes;

/// Prelude module, contains the most needed helpers from this library.
pub mod prelude {
    pub use crate::container_attributes::*;
    pub use crate::field_attributes::*;
}
