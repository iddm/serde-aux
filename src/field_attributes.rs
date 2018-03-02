#[cfg(feature = "chrono")]
use chrono;
use serde;

use std::str::FromStr;
use std::fmt::Display;

use serde::{Deserialize, Deserializer};

/// Deserializes a chrono::DateTime<Utc> from a milliseconds time stamp. Useful when the data is coming from a number
/// which is not a seconds time stamp but milliseconds one. It also handles the string to number conversion if the
/// data was passed as a string with number inside like "1519927261900".
///
/// # Example:
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// extern crate serde_json;
/// extern crate serde_aux;
/// extern crate serde;
/// extern crate chrono;
///
/// use chrono::prelude::*;
/// use serde_aux::prelude::*;
///
/// #[derive(Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_datetime_utc_from_milliseconds")]
///     time: DateTime<Utc>,
/// }
/// fn main() {
///     // Note, the the current implementation does not check if it the original was not a number.
///     let s = r#" { "time": "1519927261900" } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.time.timestamp(), 1519927261);
///     assert_eq!(a.time.timestamp_subsec_millis(), 900);
/// }
/// ```
#[cfg(feature = "chrono")]
pub fn deserialize_datetime_utc_from_milliseconds<'de, D>(
    deserializer: D,
) -> Result<chrono::DateTime<chrono::Utc>, D::Error>
where
    D: Deserializer<'de>,
{
    use chrono::prelude::*;

    let number = deserialize_number_from_string::<i64, D>(deserializer)?;
    let seconds = number / 1000;
    let millis = (number % 1000) as u32;
    let nanos = millis * 1_000_000;

    Ok(DateTime::<Utc>::from_utc(
        NaiveDateTime::from_timestamp(seconds, nanos),
        Utc,
    ))
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
/// use serde_aux::prelude::*;
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_number_from_string")]
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
/// For making it work with strong types you must implement `FromStr` trait. It is quite simple.
///
/// # Example
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
/// use serde_aux::prelude::*;
///
/// #[derive(Serialize, Deserialize, Debug, PartialEq)]
/// struct IntId(u64);
///
/// impl FromStr for IntId {
///     type Err = ParseIntError;
///
///     fn from_str(s: &str) -> Result<IntId, Self::Err> {
///         Ok(IntId(u64::from_str(s)?))
///     }
/// }
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_number_from_string")]
///     int_id: IntId,
/// }
/// fn main() {
///     let s = r#"{ "int_id": "123" }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.int_id.0, 123);
///
///     let s = r#"{ "int_id": 444 }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.int_id.0, 444);
///
/// }
/// ```
pub fn deserialize_number_from_string<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + serde::Deserialize<'de>,
    <T as FromStr>::Err: Display,
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

/// Deserializes boolean from a anything (string, number, boolean). If input is a string,
/// it is expected, that it is possible to convert it to a number. The return boolean is
/// true if the number was `1` or `1.0` after parsing.
///
/// # Example
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// extern crate serde_json;
/// extern crate serde_aux;
/// extern crate serde;
///
/// use serde_aux::prelude::*;
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_bool_from_anything")]
///     boolean: bool,
/// }
/// fn main() {
///     let s = r#"{ "boolean": 1.0 }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.boolean);
///
///     let s = r#"{ "boolean": 0.0 }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(!a.boolean);
///
///     let s = r#"{ "boolean": 2.3 }"#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
///     let s = r#"{ "boolean": 1 }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.boolean);
///
///     let s = r#"{ "boolean": 0 }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(!a.boolean);
///
///     let s = r#"{ "boolean": 2 }"#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
///     let s = r#"{ "boolean": "1.0" }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.boolean);
///
///     let s = r#"{ "boolean": "0.0" }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(!a.boolean);
///
///     let s = r#"{ "boolean": "2.3" }"#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
///     let s = r#"{ "boolean": "1" }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.boolean);
///
///     let s = r#"{ "boolean": "0" }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(!a.boolean);
///
///     let s = r#"{ "boolean": "2" }"#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
///     let s = r#"{ "boolean": "foo" }"#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// }
/// ```
pub fn deserialize_bool_from_anything<'de, D>(deserializer: D) -> Result<bool, D::Error>
where
    D: Deserializer<'de>,
{
    use std::f64::EPSILON;

    #[derive(Deserialize)]
    #[serde(untagged)]
    enum AnythingOrBool {
        String(String),
        Int(i64),
        Float(f64),
        Boolean(bool),
    }

    match AnythingOrBool::deserialize(deserializer)? {
        AnythingOrBool::Boolean(b) => Ok(b),
        AnythingOrBool::Int(i) => match i {
            1 => Ok(true),
            0 => Ok(false),
            _ => Err(serde::de::Error::custom("The number is neither 1 nor 0")),
        },
        AnythingOrBool::Float(f) => {
            if (f - 1.0f64).abs() < EPSILON {
                Ok(true)
            } else if f == 0.0f64 {
                Ok(false)
            } else {
                Err(serde::de::Error::custom(
                    "The number is neither 1.0 nor 0.0",
                ))
            }
        }
        AnythingOrBool::String(string) => {
            if let Ok(b) = string.parse::<bool>() {
                Ok(b)
            } else if let Ok(i) = string.parse::<i64>() {
                match i {
                    1 => Ok(true),
                    0 => Ok(false),
                    _ => Err(serde::de::Error::custom("The number is neither 1 nor 0")),
                }
            } else if let Ok(f) = string.parse::<f64>() {
                if (f - 1.0f64).abs() < EPSILON {
                    Ok(true)
                } else if f == 0.0f64 {
                    Ok(false)
                } else {
                    Err(serde::de::Error::custom(
                        "The number is neither 1.0 nor 0.0",
                    ))
                }
            } else {
                Err(serde::de::Error::custom(format!(
                    "Could not parse boolean from a string: {}",
                    string
                )))
            }
        }
    }
}
