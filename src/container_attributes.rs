use serde::{Deserialize, Deserializer};
use serde::de::{DeserializeOwned, Error};

/// Deserializes a struct without checking for the fields case sensititivity.
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
/// use serde_aux::prelude::*;
///
/// #[derive(Deserialize, Debug)]
/// struct AnotherStruct {
///     aaa: String,
/// }
/// #[derive(Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_struct_case_insensitive")]
///     another_struct: AnotherStruct,
/// }
///
/// fn main() {
///     let s = r#"{ "another_struct": { "AaA": "Test example" } }"#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.another_struct.aaa, "Test example");
/// }
/// ```
pub fn deserialize_struct_case_insensitive<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    T: DeserializeOwned,
    D: Deserializer<'de>,
{
    use serde_json::Value;

    use std::collections::BTreeMap as Map;

    let map = Map::<String, Value>::deserialize(deserializer)?;
    let lower = map.into_iter()
        .map(|(k, v)| (k.to_lowercase(), v))
        .collect();
    T::deserialize(Value::Object(lower)).map_err(Error::custom)
}

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
/// use serde_aux::prelude::*;
///
/// #[derive(Serialize, Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_string_from_number")]
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
