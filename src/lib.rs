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
///     #[serde(deserialize_with = "serde_aux::deserialize_number_from_string")]
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
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "serde_aux::deserialize_bool_from_anything")]
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

/// This contains both serialization and deserialization a enum into/from numbers.
/// The [reference implementation] does not work if your enum has negative values.
/// This `enum_number` handles this also.
///
/// # Example
///
/// ```rust
/// #[macro_use]
/// extern crate serde_derive;
/// #[macro_use]
/// extern crate serde_aux;
/// extern crate serde_json;
/// extern crate serde;
///
/// serde_aux_enum_number_declare!(TestEnum {
///     Up = 1,
///     None = 0,
///     Down = -1,
/// });
///
/// fn main() {
///     let s = r#"1"#;
///     let a: TestEnum = serde_json::from_str(s).unwrap();
///     assert_eq!(a, TestEnum::Up);
///
///     let s = r#"0"#;
///     let a: TestEnum = serde_json::from_str(s).unwrap();
///     assert_eq!(a, TestEnum::None);
///
///     let s = r#"-1"#;
///     let a: TestEnum = serde_json::from_str(s).unwrap();
///     assert_eq!(a, TestEnum::Down);
///
///     let s = r#"5"#;
///     assert!(serde_json::from_str::<TestEnum>(s).is_err());
/// }
/// ```

#[macro_export]
macro_rules! serde_aux_enum_number_declare {
    ($name:ident { $($variant:ident = $value:expr, )* }) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
        pub enum $name {
            $($variant = $value,)*
        }

        impl<'de> serde::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where D: serde::Deserializer<'de>
            {
                use std::fmt;
                struct Visitor;

                impl<'de> serde::de::Visitor<'de> for Visitor {
                    type Value = $name;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("integer")
                    }

                    fn visit_i64<E>(self, value: i64) -> Result<$name, E>
                        where E: serde::de::Error
                    {
                        // Rust does not come with a simple way of converting a
                        // number to an enum, so use a big `match`.
                        match value {
                            $( $value => Ok($name::$variant), )*
                            _ => Err(E::custom(
                                format!("unknown {} value: {}",
                                stringify!($name), value))),
                        }
                    }

                    fn visit_u64<E>(self, value: u64) -> Result<$name, E>
                        where E: serde::de::Error
                    {
                        self.visit_i64(value as i64)
                    }
                }

                // Deserialize the enum from a i64.
                deserializer.deserialize_i64(Visitor)
            }
        }
    }
}
