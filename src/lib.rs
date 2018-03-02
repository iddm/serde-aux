//! # serde-aux
//!
//! A serde auxiliary library.

#![deny(missing_docs)]
#![deny(warnings)]

#[cfg(feature = "chrono")]
extern crate chrono;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;

/// Contains helpers for the fields.
pub mod field_attributes;
/// Contains helpers for the containers.
pub mod container_attributes;

/// Prelude module, contains the most needed helpers from this library.
pub mod prelude {
    pub use field_attributes::*;
    pub use container_attributes::*;
}
