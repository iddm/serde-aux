//! # serde-aux
//!
//! A serde auxiliary library.

#![deny(missing_docs)]
#![deny(warnings)]

extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;

use std::str::FromStr;

use serde::{Deserialize, Deserializer};

/// Deserializes string from a number. If the original value is a number value, it will be converted to a string.
///
/// # Example:
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// extern crate serde_json;
/// extern crate serde_aux;
/// extern crate serde;
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "serde_aux::deserialize_string_from_number")]
///     number_as_string: String,
/// }
/// fn main() {
///     // Note, the the current implementation does not check if it the original was not a number.
///     let s = r#" { "number_as_string": "foo" } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_as_string, "foo");
///
///     let s = r#" { "number_as_string": -13 } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_as_string, "-13");
/// }
/// ```
pub fn deserialize_string_from_number<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum StringOrInt {
        String(String),
        Number(i64),
    }

    match StringOrInt::deserialize(deserializer)? {
        StringOrInt::String(s) => Ok(s),
        StringOrInt::Number(i) => Ok(i.to_string()),
    }
}

/// Deserializes a number from string or a number.
///
/// # Example:
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// extern crate serde_json;
/// extern crate serde_aux;
/// extern crate serde;
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "serde_aux::deserialize_number_from_string")]
///     number_from_string: u64,
/// }
/// fn main() {
///     // Note, the the current implementation does not check if it the original was not a number.
///     let s = r#" { "number_from_string": "123" } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_from_string, 123);
///
///     let s = r#" { "number_from_string": 444 } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_from_string, 444);
/// }
/// ```
///
/// For making it work with strong types you must implement `FromStr` trait. It is quite simple:
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// extern crate serde_json;
/// extern crate serde_aux;
/// extern crate serde;
///
/// use std::str::FromStr;
/// use std::num::{ParseIntError, ParseFloatError};
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct IntId(u64);
///
/// impl FromStr for IntId {
///     type Err = ParseIntError;
///
///     fn from_str(s: &str) -> Result<IntId, Self::Err> {
///         Ok(IntId(u64::from_str(s)?))
///     }
/// }
/// fn main() {
///
/// }
/// ```


pub fn deserialize_number_from_string<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + serde::Deserialize<'de>,
    <T as std::str::FromStr>::Err: std::fmt::Display,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum StringOrInt<T> {
        String(String),
        Number(T),
    }

    match StringOrInt::<T>::deserialize(deserializer)? {
        StringOrInt::String(s) => s.parse::<T>().map_err(serde::de::Error::custom),
        StringOrInt::Number(i) => Ok(i),
    }
}
