use std::fmt::Display;
use std::str::FromStr;

#[cfg(feature = "chrono")]
use serde::de::Error;
use serde::{Deserialize, Deserializer};

/// Allows a `bool` field to be defaulted to `true`, rather than the normal
/// default of `false`. Useful for fields where the default value should be `true`.
///
/// Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default)]
///     default_false: bool,
///     #[serde(default = "bool_true")]
///     default_true: bool,
/// }
///
/// let s = r#" { } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.default_false);
/// assert!(a.default_true);
/// ```
#[inline]
pub fn bool_true() -> bool {
    true
}

/// Allows compact setting `u16` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_u16::<30>")]
///     default_30: u16,
///     #[serde(default)]
///     default_zero: u16,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, 30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_u16<const V: u16>() -> u16 {
    V
}

/// Allows compact setting `u32` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_u32::<30>")]
///     default_30: u32,
///     #[serde(default)]
///     default_zero: u32,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, 30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_u32<const V: u32>() -> u32 {
    V
}

/// Allows compact setting `u64` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_u64::<30>")]
///     default_30: u64,
///     #[serde(default)]
///     default_zero: u64,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, 30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_u64<const V: u64>() -> u64 {
    V
}

/// Allows compact setting `i16` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_i16::<-30>")]
///     default_30: i16,
///     #[serde(default)]
///     default_zero: i16,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, -30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_i16<const V: i16>() -> i16 {
    V
}

/// Allows compact setting `i32` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_i32::<-30>")]
///     default_30: i32,
///     #[serde(default)]
///     default_zero: i32,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, -30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_i32<const V: i32>() -> i32 {
    V
}

/// Allows compact setting `i64` field default value.
///
/// # Example
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(default = "default_i64::<-30>")]
///     default_30: i64,
///     #[serde(default)]
///     default_zero: i64,
/// }
///
/// let s = r#"{}"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.default_30, -30);
/// assert_eq!(a.default_zero, 0);
/// ```
#[inline]
pub const fn default_i64<const V: i64>() -> i64 {
    V
}

/// Deserializes a `chrono::DateTime<Utc>` from a milliseconds time stamp. Useful when the data is coming from a number
/// which is not a seconds time stamp but milliseconds one. It also handles the string to number conversion if the
/// data was passed as a string with number inside like **"1519927261900"**.
///
/// # Example:
///
/// ```rust
/// use chrono::prelude::*;
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_datetime_utc_from_milliseconds")]
///     time: DateTime<Utc>,
/// }
///
/// let s = r#" { "time": "1519927261900" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.time.timestamp(), 1519927261);
/// assert_eq!(a.time.timestamp_subsec_millis(), 900);
/// ```
#[cfg(feature = "chrono")]
pub fn deserialize_datetime_utc_from_milliseconds<'de, D>(
    deserializer: D,
) -> Result<chrono::DateTime<chrono::Utc>, D::Error>
where
    D: Deserializer<'de>,
{
    use chrono::prelude::*;

    let millis = deserialize_number_from_string::<i64, D>(deserializer)?;
    DateTime::<Utc>::from_timestamp_millis(millis)
        .ok_or_else(|| D::Error::custom("Couldn't parse the timestamp"))
}

/// Deserializes a `chrono::DateTime<Utc>` from a seconds time stamp.
/// It also handles the string to number conversion if the
/// data was passed as a string with number inside like **"1519927261"**.
///
/// # Example:
///
/// ```rust
/// use chrono::prelude::*;
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_datetime_utc_from_seconds")]
///     time: DateTime<Utc>,
/// }
///
/// let s = r#" { "time": "1519927261" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.time.timestamp(), 1519927261);
/// assert_eq!(a.time.timestamp_subsec_millis(), 0);
/// ```
#[cfg(feature = "chrono")]
pub fn deserialize_datetime_utc_from_seconds<'de, D>(
    deserializer: D,
) -> Result<chrono::DateTime<chrono::Utc>, D::Error>
where
    D: Deserializer<'de>,
{
    use chrono::prelude::*;

    let seconds = deserialize_number_from_string::<i64, D>(deserializer)?;
    DateTime::<Utc>::from_timestamp(seconds, 0)
        .ok_or_else(|| D::Error::custom("Couldn't parse the timestamp"))
}

/// Deserializes a number from string or a number.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_number_from_string")]
///     number_from_string: u64,
/// }
///
/// let s = r#" { "number_from_string": "123" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.number_from_string, 123);
///
/// let s = r#" { "number_from_string": 444 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.number_from_string, 444);
/// ```
///
/// For making it work with strong types you must implement `FromStr` trait. It is quite simple.
///
/// # Example
///
/// ```rust
/// use std::str::FromStr;
/// use std::num::{ParseIntError, ParseFloatError};
///
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug, PartialEq)]
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
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_number_from_string")]
///     int_id: IntId,
/// }
///
/// let s = r#"{ "int_id": "123" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.int_id.0, 123);
///
/// let s = r#"{ "int_id": 444 }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.int_id.0, 444);
/// ```
pub fn deserialize_number_from_string<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de>,
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

/// Deserializes an option number from string or a number.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_option_number_from_string")]
///     option_num: Option<f32>,
///     #[serde(default, deserialize_with = "deserialize_option_number_from_string")]
///     missing: Option<i32>
/// }
/// fn serde_qs_eq(s: &str, result: Option<f32>) {
///     let a: MyStruct = serde_qs::from_str(s).unwrap();
///     assert_eq!(a.option_num, result);
///     assert_eq!(a.missing, None);
/// }
/// fn serde_qs_err(s: &str) {
///     assert!(serde_qs::from_str::<MyStruct>(s).is_err());
/// }
/// fn serde_json_eq(s: &str, result: Option<f32>) {
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.option_num, result);
///     assert_eq!(a.missing, None);
/// }
/// fn serde_json_err(s: &str) {
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// }
///
/// serde_qs_eq("option_num=1", Some(1.0));
/// serde_qs_eq("option_num=-1", Some(-1.0));
/// serde_qs_eq("option_num=0.1", Some(0.1));
/// serde_qs_eq("option_num=-0.1", Some(-0.1));
/// serde_qs_eq("option_num=", None);
/// serde_qs_eq("option_num", None);
///
/// serde_qs_err("option_num=true");
/// serde_qs_err("option_num=a");
/// serde_qs_err("option_num[a]=");
/// serde_qs_err("option_num[]=");
///
/// serde_json_eq(r#" { "option_num": "1" } "#, Some(1.0));
/// serde_json_eq(r#" { "option_num": "-1" } "#, Some(-1.0));
/// serde_json_eq(r#" { "option_num": "0.1" } "#, Some(0.1));
/// serde_json_eq(r#" { "option_num": "-0.1" } "#, Some(-0.1));
/// serde_json_eq(r#" { "option_num": 1 } "#, Some(1.0));
/// serde_json_eq(r#" { "option_num": -1 } "#, Some(-1.0));
/// serde_json_eq(r#" { "option_num": 0.1 } "#, Some(0.1));
/// serde_json_eq(r#" { "option_num": -0.1 } "#, Some(-0.1));
/// serde_json_eq(r#" { "option_num": "" } "#, None);
/// serde_json_eq(r#" { "option_num": null } "#, None);
///
/// serde_json_err(r#" { "option_num": true } "#);
/// serde_json_err(r#" { "option_num": "a" } "#);
/// serde_json_err(r#" { "option_num": {} } "#);
/// serde_json_err(r#" { "option_num": [] } "#);
/// ```
pub fn deserialize_option_number_from_string<'de, T, D>(
    deserializer: D,
) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de>,
    <T as FromStr>::Err: Display,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum NumericOrNull<'a, T> {
        Str(&'a str),
        String(String),
        FromStr(T),
        Null,
    }

    match NumericOrNull::<T>::deserialize(deserializer)? {
        NumericOrNull::Str(s) => match s {
            "" => Ok(None),
            _ => T::from_str(s).map(Some).map_err(serde::de::Error::custom),
        },
        NumericOrNull::String(s) => match s.as_str() {
            "" => Ok(None),
            _ => T::from_str(&s).map(Some).map_err(serde::de::Error::custom),
        },
        NumericOrNull::FromStr(i) => Ok(Some(i)),
        NumericOrNull::Null => Ok(None),
    }
}

macro_rules! wrap_option_number_from_string_fn {
    (
        $(#[doc = $doc:tt])*
        $func:ident,
        $res:ty
    ) => {
        $(#[doc = $doc])*
        pub fn $func<'de, T, D>(deserializer: D) -> Result<$res, D::Error>
        where
            D: Deserializer<'de>,
            T: FromStr + Deserialize<'de>,
            <T as FromStr>::Err: Display,
        {
            #[derive(Deserialize)]
            #[serde(untagged)]
            enum NumericOrNull<'a, T> {
                Str(&'a str),
                String(String),
                FromStr(T),
                Null,
            }

            match NumericOrNull::<T>::deserialize(deserializer)? {
                NumericOrNull::Str(s) => match s {
                    "" => Ok(None.into()),
                    _ => T::from_str(s)
                        .map(|i| Some(i).into())
                        .map_err(serde::de::Error::custom),
                },
                NumericOrNull::String(s) => match s.as_str() {
                    "" => Ok(None.into()),
                    _ => T::from_str(&s)
                        .map(|i| Some(i).into())
                        .map_err(serde::de::Error::custom),
                },
                NumericOrNull::FromStr(i) => Ok(Some(i).into()),
                NumericOrNull::Null => Ok(None.into()),
            }
        }
    };
}
wrap_option_number_from_string_fn!(
    /// Deserializes a `Cell` option number from string or a number. Same logic as [`"deserialize_option_number_from_string"`](https://docs.rs/serde-aux/latest/serde_aux/field_attributes/fn.deserialize_option_number_from_string.html).
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::cell::Cell;
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "deserialize_cell_option_number_from_string")]
    ///     v: Cell<Option<f32>>
    /// }
    ///
    /// let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    /// assert_eq!(a.v, Cell::new(Some(-0.1)));
    /// ```
    deserialize_cell_option_number_from_string,
    std::cell::Cell<Option<T>>
);
wrap_option_number_from_string_fn!(
    /// Deserializes a `RefCell` option number from string or a number. Same logic as [`"deserialize_option_number_from_string"`](https://docs.rs/serde-aux/latest/serde_aux/field_attributes/fn.deserialize_option_number_from_string.html).
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::cell::RefCell;
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_ref_cell_option_number_from_string")]
    ///     v: RefCell<Option<f32>>
    /// }
    ///
    /// let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    /// assert_eq!(a.v, RefCell::new(Some(-0.1)));
    /// ```
    deserialize_ref_cell_option_number_from_string,
    std::cell::RefCell<Option<T>>
);
wrap_option_number_from_string_fn!(
    /// Deserializes a `Mutex` option number from string or a number. Same logic as [`"deserialize_option_number_from_string"`](https://docs.rs/serde-aux/latest/serde_aux/field_attributes/fn.deserialize_option_number_from_string.html).
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::sync::Mutex;
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_mutex_option_number_from_string")]
    ///     v: Mutex<Option<f32>>
    /// }
    ///
    /// let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    /// assert_eq!(*a.v.lock().unwrap(), Some(-0.1));
    /// ```
    deserialize_mutex_option_number_from_string,
    std::sync::Mutex<Option<T>>
);
wrap_option_number_from_string_fn!(
    /// Deserializes a `RwLock` option number from string or a number. Same logic as [`"deserialize_option_number_from_string"`](https://docs.rs/serde-aux/latest/serde_aux/field_attributes/fn.deserialize_option_number_from_string.html).
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::sync::RwLock;
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_rw_lock_option_number_from_string")]
    ///     v: RwLock<Option<f32>>
    /// }
    ///
    /// let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    /// assert_eq!(*a.v.read().unwrap(), Some(-0.1));
    /// ```
    deserialize_rw_lock_option_number_from_string,
    std::sync::RwLock<Option<T>>
);

/// Deserializes boolean from anything (string, number, boolean). If input is a string,
/// it is expected, that it is possible to convert it to a number. The return boolean is
/// `true` if the number was either `1` or `1.0` after parsing.
///
/// # Example
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_bool_from_anything")]
///     boolean: bool,
/// }
///
/// let s = r#"{ "boolean": 1.0 }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": 0.0 }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": 2.3 }"#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
/// let s = r#"{ "boolean": 1 }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": 0 }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": 2 }"#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
/// let s = r#"{ "boolean": "1.0" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": "0.0" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": "2.3" }"#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
/// let s = r#"{ "boolean": "1" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": "0" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": "TRUE" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": "FALSE" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": "TruE" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": "fAlsE" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": "true" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.boolean);
///
/// let s = r#"{ "boolean": "false" }"#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(!a.boolean);
///
/// let s = r#"{ "boolean": "2" }"#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
///
/// let s = r#"{ "boolean": "foo" }"#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// ```
pub fn deserialize_bool_from_anything<'de, D>(deserializer: D) -> Result<bool, D::Error>
where
    D: Deserializer<'de>,
{
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
            if (f - 1.0f64).abs() < f64::EPSILON {
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
            if let Ok(b) = string.to_lowercase().parse::<bool>() {
                Ok(b)
            } else if let Ok(i) = string.parse::<i64>() {
                match i {
                    1 => Ok(true),
                    0 => Ok(false),
                    _ => Err(serde::de::Error::custom("The number is neither 1 nor 0")),
                }
            } else if let Ok(f) = string.parse::<f64>() {
                if (f - 1.0f64).abs() < f64::EPSILON {
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

/// Deserializes string from a number. If the original value is a number value,
/// it will be converted to a string.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_string_from_number")]
///     number_as_string: String,
/// }
///
/// let s = r#" { "number_as_string": "foo" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.number_as_string, "foo");
///
/// let s = r#" { "number_as_string": -13 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.number_as_string, "-13");
///
/// let s = r#" { "number_as_string": 24.0034 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.number_as_string, "24.0034");
/// ```
pub fn deserialize_string_from_number<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum StringOrNumber {
        String(String),
        Number(i64),
        Float(f64),
    }

    match StringOrNumber::deserialize(deserializer)? {
        StringOrNumber::String(s) => Ok(s),
        StringOrNumber::Number(i) => Ok(i.to_string()),
        StringOrNumber::Float(f) => Ok(f.to_string()),
    }
}

/// Deserializes default value from nullable value. If the original value is `null`,
/// `Default::default()` is used.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_default_from_null")]
///     null_as_default: u64,
/// }
///
/// let s = r#" { "null_as_default": 42 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.null_as_default, 42);
///
/// let s = r#" { "null_as_default": null } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.null_as_default, 0);
///
/// let s = r#" { "null_as_default": "wrong_type" } "#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// ```
pub fn deserialize_default_from_null<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    Ok(Option::deserialize(deserializer)?.unwrap_or_default())
}

/// Deserializes default value from nullable value or empty object. If the original value is `null` or `{}`,
/// `Default::default()` is used.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_default_from_empty_object")]
///     empty_as_default: Option<MyInnerStruct>,
/// }
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyInnerStruct {
///     mandatory: u64,
/// }
///
/// let s = r#" { "empty_as_default": { "mandatory": 42 } } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.empty_as_default.unwrap().mandatory, 42);
///
/// let s = r#" { "empty_as_default": null } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.empty_as_default.is_none());
///
/// let s = r#" { "empty_as_default": {} } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert!(a.empty_as_default.is_none());
///
/// let s = r#" { "empty_as_default": { "unknown": 42 } } "#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// ```
pub fn deserialize_default_from_empty_object<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    #[derive(Debug, Deserialize)]
    #[serde(deny_unknown_fields)]
    struct EmptyObject {}

    #[derive(Debug, Deserialize)]
    #[serde(untagged)]
    enum EmptyOrNot<Y> {
        NonEmpty(Y),
        Empty(EmptyObject),
        Null,
    }

    let empty_or_not: EmptyOrNot<T> = EmptyOrNot::deserialize(deserializer)?;

    match empty_or_not {
        EmptyOrNot::NonEmpty(e) => Ok(e),
        _ => Ok(T::default()),
    }
}

/// Deserializes a comma separated string into a `Vec<T>`.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_vec_from_string_or_vec")]
///     list: Vec<i32>,
/// }
///
/// let s = r#" { "list": "1,2,3,4" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
///
/// let s = r#" { "list": [1,2,3,4] } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
/// ```
pub fn deserialize_vec_from_string_or_vec<'de, T, D>(deserializer: D) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + Deserialize<'de> + 'static,
    <T as FromStr>::Err: std::fmt::Display,
{
    StringOrVecToVec::default().into_deserializer()(deserializer)
}

/// Deserialize to primary or fallback type.
///
/// This helper function will attempt to deserialize to the primary type first,
/// and if that fails it will attempt to deserialize to the fallback type. If
/// both fail, it will return an error.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_to_type_or_fallback")]
///     i64_or_f64: Result<i64, f64>,
///     #[serde(deserialize_with = "deserialize_to_type_or_fallback")]
///     f64_or_string: Result<f64, String>,
/// }
///
/// let s = r#" { "i64_or_f64": 1, "f64_or_string": 1 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.i64_or_f64, Ok(1));
/// assert_eq!(a.f64_or_string, Ok(1.0));
///
/// let s = r#" { "i64_or_f64": 1.0, "f64_or_string": 1.0 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.i64_or_f64, Err(1.0));
/// assert_eq!(a.f64_or_string, Ok(1.0));
///
/// let s = r#" { "i64_or_f64": 1.0, "f64_or_string": "foo" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.i64_or_f64, Err(1.0));
/// assert_eq!(a.f64_or_string, Err(String::from("foo")));
///
/// let s = r#" { "i64_or_f64": "foo", "f64_or_string": "foo" } "#;
/// assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// ```
pub fn deserialize_to_type_or_fallback<'de, D, T, F>(
    deserializer: D,
) -> Result<Result<T, F>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
    F: Deserialize<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum DeEither<T, F> {
        Type(T),
        Fallback(F),
    }

    DeEither::<T, F>::deserialize(deserializer).map(|de| match de {
        DeEither::Type(t) => Ok(t),
        DeEither::Fallback(f) => Err(f),
    })
}

/// Deserialize to a given type, while ignoring any invalid fields.
///
/// This helper function will attempt to deserialize to the given type, and if
/// it fails it will return `None`, therefore never failing. This is different
/// from deserializing directly to `Option<T>`, because this would return `None`
/// only for empty fields, while it would return an error for invalid fields.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_to_type_or_none")]
///     opt_f64: Option<f64>,
/// }
///
/// let s = r#" { "opt_f64": 1 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.opt_f64, Some(1.0));
///
/// let s = r#" { "opt_f64": 1.0 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.opt_f64, Some(1.0));
///
/// let s = r#" { "opt_f64": "foo" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.opt_f64, None);
/// ```
pub fn deserialize_to_type_or_none<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    Option<T>: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer).or_else(|_| Ok(None))
}

/// Deserialize to a given type, while returning invalid fields as `String`.
///
/// This helper function will attempt to deserialize to the given type, and if
/// it fails it will return the invalid field lossily converted to `String`,
/// therefore never failing.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_to_type_or_string_lossy")]
///     f64_or_string_lossy: Result<f64, String>,
/// }
///
/// let s = r#" { "f64_or_string_lossy": 1 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.f64_or_string_lossy, Ok(1.0));
///
/// let s = r#" { "f64_or_string_lossy": 1.0 } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.f64_or_string_lossy, Ok(1.0));
///
/// let s = r#" { "f64_or_string_lossy": "foo" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(a.f64_or_string_lossy, Err(String::from("foo")));
/// ```
pub fn deserialize_to_type_or_string_lossy<'de, D, T>(
    deserializer: D,
) -> Result<Result<T, String>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    let value = serde_value::Value::deserialize(deserializer)?;
    Ok(T::deserialize(value.clone()).map_err(|_| match value {
        serde_value::Value::Bool(b) => b.to_string(),
        serde_value::Value::U8(u) => u.to_string(),
        serde_value::Value::U16(u) => u.to_string(),
        serde_value::Value::U32(u) => u.to_string(),
        serde_value::Value::U64(u) => u.to_string(),
        serde_value::Value::I8(i) => i.to_string(),
        serde_value::Value::I16(i) => i.to_string(),
        serde_value::Value::I32(i) => i.to_string(),
        serde_value::Value::I64(i) => i.to_string(),
        serde_value::Value::F32(f) => f.to_string(),
        serde_value::Value::F64(f) => f.to_string(),
        serde_value::Value::Char(c) => c.to_string(),
        serde_value::Value::String(s) => s,
        serde_value::Value::Unit => String::new(),
        serde_value::Value::Option(opt) => {
            format!("{:?}", opt)
        }
        serde_value::Value::Newtype(nt) => {
            format!("{:?}", nt)
        }
        serde_value::Value::Seq(seq) => format!("{:?}", seq),
        serde_value::Value::Map(map) => format!("{:?}", map),
        serde_value::Value::Bytes(v) => String::from_utf8_lossy(&v).into_owned(),
    }))
}

/// Create a parser quickly.
///
/// ```
/// use serde_aux::prelude::*;
/// use std::str::FromStr;
///
/// serde_aux::StringOrVecToVecParser!(parse_between_commas, |c| { c == ',' }, true);
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "parse_between_commas")]
///     list: Vec<i32>,
/// }
///
/// let s = r#" { "list": "1,2,3,4" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
///
/// let s = r#" { "list": [1,2,3,4] } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
///
///
/// serde_aux::StringOrVecToVecParser!(u8, parse_hex_with_spaces, ' ', |s| { u8::from_str_radix(s, 16) }, true);
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStructHex {
///     #[serde(deserialize_with = "parse_hex_with_spaces")]
///     list: Vec<u8>,
/// }
///
/// let s = r#" { "list": "a1 b2 c3 d4 " } "#;
/// let a: MyStructHex = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[0xa1, 0xb2, 0xc3, 0xd4]);
///
/// let s = r#" { "list": "a1 b2 c3  d4   " } "#;
/// let a: MyStructHex = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[0xa1, 0xb2, 0xc3, 0xd4]);
/// ```
#[macro_export]
macro_rules! StringOrVecToVecParser {
    ($name:ident, $separator:expr, $skip_empty:expr) => {
        fn $name<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
        where
            D: serde::Deserializer<'de>,
            T: FromStr + serde::Deserialize<'de> + 'static,
            <T as FromStr>::Err: std::fmt::Display,
        {
            let mut parser = $crate::field_attributes::StringOrVecToVec::with_separator($separator);
            parser.skip_empty($skip_empty);
            parser.into_deserializer()(deserializer)
        }
    };

    ($t:ty, $name:ident, $pattern:expr, $converter:expr, $skip_empty:expr) => {
        fn $name<'de, D>(deserializer: D) -> Result<Vec<$t>, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            $crate::field_attributes::StringOrVecToVec::new($pattern, $converter, $skip_empty)
                .into_deserializer()(deserializer)
        }
    };
}

/// Builder to create a parser, that parses a separated string or a vec into a vec.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
/// use std::str::FromStr;
///
/// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
/// where
///     D: serde::Deserializer<'de>,
///     T: FromStr + serde::Deserialize<'de> + 'static,
///     <T as FromStr>::Err: std::fmt::Display,
/// {
///     StringOrVecToVec::default().into_deserializer()(deserializer)
/// }
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "parser")]
///     list: Vec<i32>,
/// }
///
/// let s = r#" { "list": "1,2,3,4" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
///
/// let s = r#" { "list": [1,2,3,4] } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
pub struct StringOrVecToVec<'a, T, E> {
    separator: Pattern<'a>,
    parser: Box<StringOrVecParser<T, E>>,
    skip_empty: bool,
}

/// A functor returning a [`Result`] of parsing a string into a vector
/// of objects of type `T`.
pub type StringOrVecParser<T, E> = dyn FnMut(&str) -> Result<T, E>;

/// Pattern on which a string can be split.
pub enum Pattern<'a> {
    /// Split on a matching char
    Char(char),
    /// Split on a matching str
    Str(&'a str),
    /// Split if a char matches the predicate
    Pred(Box<dyn Fn(char) -> bool>),
    /// Multiple patterns
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::str::FromStr;
    ///
    /// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
    /// where
    ///     D: serde::Deserializer<'de>,
    ///     T: FromStr + serde::Deserialize<'de> + 'static,
    ///     <T as FromStr>::Err: std::fmt::Display,
    /// {
    ///     StringOrVecToVec::with_separator(vec![Pattern::Char('+'), Pattern::Char('-')]).into_deserializer()(deserializer)
    /// }
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "parser")]
    ///     list: Vec<i32>,
    /// }
    ///
    /// let s = r#" { "list": "1-2+3-4" } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    ///
    /// let s = r#" { "list": [1,2,3,4] } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    /// ```
    Multiple(Vec<Pattern<'a>>),
}

impl From<char> for Pattern<'_> {
    fn from(c: char) -> Self {
        Pattern::Char(c)
    }
}

impl<'a> From<&'a str> for Pattern<'a> {
    fn from(s: &'a str) -> Self {
        Pattern::Str(s)
    }
}

impl<'a> From<Vec<Pattern<'a>>> for Pattern<'a> {
    fn from(patterns: Vec<Pattern<'a>>) -> Self {
        Pattern::Multiple(patterns)
    }
}

/// # Example
///
/// ```rust
/// use serde_aux::prelude::*;
/// use std::str::FromStr;
///
/// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
/// where
///     D: serde::Deserializer<'de>,
///     T: FromStr + serde::Deserialize<'de> + 'static,
///     <T as FromStr>::Err: std::fmt::Display,
/// {
///     StringOrVecToVec::with_separator(vec!['-', '+'].into_iter().collect::<Pattern>()).into_deserializer()(deserializer)
/// }
///
/// #[derive(serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "parser")]
///     list: Vec<i32>,
/// }
///
/// let s = r#" { "list": "1-2+3-4" } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
///
/// let s = r#" { "list": [1,2,3,4] } "#;
/// let a: MyStruct = serde_json::from_str(s).unwrap();
/// assert_eq!(&a.list, &[1, 2, 3, 4]);
/// ```
impl<'a> std::iter::FromIterator<Pattern<'a>> for Pattern<'a> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Pattern<'a>>,
    {
        Pattern::Multiple(iter.into_iter().collect())
    }
}

impl std::iter::FromIterator<char> for Pattern<'_> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = char>,
    {
        Pattern::Multiple(iter.into_iter().map(Pattern::from).collect())
    }
}

impl<'a> std::iter::FromIterator<&'a str> for Pattern<'a> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a str>,
    {
        Pattern::Multiple(iter.into_iter().map(Pattern::from).collect())
    }
}

impl<P> From<P> for Pattern<'_>
where
    P: Fn(char) -> bool + 'static,
{
    fn from(pred: P) -> Self {
        Pattern::Pred(Box::new(pred))
    }
}

impl<'de, T> Default for StringOrVecToVec<'_, T, T::Err>
where
    T: FromStr + Deserialize<'de> + 'static,
    <T as FromStr>::Err: std::fmt::Display,
{
    fn default() -> Self {
        Self::new(|c| c == ',', T::from_str, false)
    }
}

impl<'a, 'de, T> StringOrVecToVec<'a, T, T::Err>
where
    T: FromStr + Deserialize<'de> + 'static,
    <T as FromStr>::Err: std::fmt::Display,
{
    /// Create a `StringOrVecToVec` builder with a custom separator. `T::from_str` is used to parse
    /// the elements of the list.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::str::FromStr;
    ///
    /// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
    /// where
    ///     D: serde::Deserializer<'de>,
    ///     T: FromStr + serde::Deserialize<'de> + 'static,
    ///     <T as FromStr>::Err: std::fmt::Display,
    /// {
    ///     StringOrVecToVec::with_separator(|c| c == '-' || c == '+').into_deserializer()(deserializer)
    /// }
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "parser")]
    ///     list: Vec<i32>,
    /// }
    ///
    /// let s = r#" { "list": "1-2+3-4" } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    ///
    /// let s = r#" { "list": [1,2,3,4] } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    /// ```
    pub fn with_separator(separator: impl Into<Pattern<'a>>) -> Self {
        Self::new(separator, T::from_str, false)
    }

    /// Sets the flag to skip empty separations.
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::str::FromStr;
    ///
    /// fn parser_skip_empty<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
    /// where
    ///     D: serde::Deserializer<'de>,
    ///     T: FromStr + serde::Deserialize<'de> + 'static,
    ///     <T as FromStr>::Err: std::fmt::Display,
    /// {
    ///     let mut parser = StringOrVecToVec::with_separator(|c| c == '-' || c == '+');
    ///     parser.skip_empty(true);
    ///     parser.into_deserializer()(deserializer)
    /// }
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStructSkipEmpty {
    ///     #[serde(deserialize_with = "parser_skip_empty")]
    ///     list: Vec<i32>,
    /// }
    ///
    /// let s = r#" { "list": "1-2+3-4--++--" } "#;
    /// let a: MyStructSkipEmpty = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    /// ```
    pub fn skip_empty(&mut self, skip_empty: bool) -> &mut Self {
        self.skip_empty = skip_empty;
        self
    }
}

impl<'a, T, E> StringOrVecToVec<'a, T, E> {
    /// Create a deserializer with a custom separator and parsing function.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::str::FromStr;
    ///
    /// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
    /// where
    ///     D: serde::Deserializer<'de>,
    ///     T: FromStr + serde::Deserialize<'de> + 'static,
    ///     <T as FromStr>::Err: std::fmt::Display,
    /// {
    ///     StringOrVecToVec::new('-', |s| s.trim().parse(), false).into_deserializer()(deserializer)
    /// }
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "parser")]
    ///     list: Vec<i32>,
    /// }
    ///
    /// let s = r#" { "list": "1 - 2    -  3-    4    " } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    ///
    /// let s = r#" { "list": [1,2,3,4] } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    /// ```
    pub fn new(
        separator: impl Into<Pattern<'a>>,
        parser: impl FnMut(&str) -> Result<T, E> + 'static,
        skip_empty: bool,
    ) -> Self {
        Self {
            separator: separator.into(),
            parser: Box::new(parser),
            skip_empty,
        }
    }

    /// Create a deserializer with a custom parsing function. The input string will be separated on
    /// `,`.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use serde_aux::prelude::*;
    /// use std::str::FromStr;
    ///
    /// fn parser<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
    /// where
    ///     D: serde::Deserializer<'de>,
    ///     T: FromStr + serde::Deserialize<'de> + 'static,
    ///     <T as FromStr>::Err: std::fmt::Display,
    /// {
    ///     StringOrVecToVec::with_parser(|s| s.trim().parse()).into_deserializer()(deserializer)
    /// }
    ///
    /// #[derive(serde::Deserialize, Debug)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "parser")]
    ///     list: Vec<i32>,
    /// }
    ///
    /// let s = r#" { "list": "1 , 2    ,  3,    4    " } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    ///
    /// let s = r#" { "list": [1,2,3,4] } "#;
    /// let a: MyStruct = serde_json::from_str(s).unwrap();
    /// assert_eq!(&a.list, &[1, 2, 3, 4]);
    /// ```
    pub fn with_parser(parser: impl FnMut(&str) -> Result<T, E> + 'static) -> Self {
        Self::new(|c| c == ',', parser, false)
    }

    /// Creates the actual deserializer from this builder.
    pub fn into_deserializer<'de, D>(
        self,
    ) -> impl FnMut(D) -> Result<Vec<T>, <D as Deserializer<'de>>::Error>
    where
        'a: 'de,
        D: Deserializer<'de>,
        T: Deserialize<'de>,
        E: std::fmt::Display,
    {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum StringOrVec<T> {
            String(String),
            Vec(Vec<T>),
        }

        let StringOrVecToVec {
            mut parser,
            separator,
            skip_empty,
        } = self;

        move |deserializer| match StringOrVec::<T>::deserialize(deserializer)? {
            StringOrVec::String(s) => Ok(separator
                .split(&s)
                .into_iter()
                .filter(|s| {
                    if skip_empty && s.is_empty() {
                        return false;
                    }
                    true
                })
                .map(&mut parser)
                .collect::<Result<Vec<_>, _>>()
                .map_err(serde::de::Error::custom)?),
            StringOrVec::Vec(v) => Ok(v),
        }
    }
}

impl Pattern<'_> {
    fn split<'b>(&self, input: &'b str) -> Vec<&'b str> {
        match self {
            Pattern::Char(c) => input.split(*c).collect(),
            Pattern::Str(s) => input.split(s).collect(),
            Pattern::Pred(p) => input.split(p).collect(),
            Pattern::Multiple(patterns) => {
                let mut split = vec![input];
                for pattern in patterns {
                    let delete_until = split.len();
                    let mut new_split = Vec::new();
                    for s in &split {
                        new_split.append(&mut pattern.split(s));
                    }

                    if !new_split.is_empty() {
                        split = split.split_off(delete_until);
                    }

                    split.append(&mut new_split);
                }
                split
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use std::{
        cell::{Cell, RefCell},
        sync::{Mutex, RwLock},
    };
    #[derive(Debug, serde::Deserialize)]
    struct MyStruct {
        #[serde(
            default,
            deserialize_with = "deserialize_cell_option_number_from_string"
        )]
        cell: Cell<Option<f32>>,
        #[serde(
            default,
            deserialize_with = "deserialize_ref_cell_option_number_from_string"
        )]
        ref_cell: RefCell<Option<f32>>,
        #[serde(
            default,
            deserialize_with = "deserialize_mutex_option_number_from_string"
        )]
        mutex: Mutex<Option<f32>>,
        #[serde(
            default,
            deserialize_with = "deserialize_rw_lock_option_number_from_string"
        )]
        rw_lock: RwLock<Option<f32>>,
    }
    macro_rules! serde_qs_eq {
        ($s:literal, $result:expr) => {
            let a: MyStruct = serde_qs::from_str($s).unwrap();
            assert_eq!(a.cell, Cell::new($result));
            assert_eq!(a.ref_cell, RefCell::new($result));
            assert_eq!(*a.mutex.lock().unwrap(), $result);
            assert_eq!(*a.rw_lock.read().unwrap(), $result);
        };
    }
    macro_rules! serde_qs_err {
        ($rest:literal) => {
            assert!(serde_qs::from_str::<MyStruct>(concat!("cell", $rest)).is_err());
            assert!(serde_qs::from_str::<MyStruct>(concat!("ref_cell", $rest)).is_err());
            assert!(serde_qs::from_str::<MyStruct>(concat!("mutex", $rest)).is_err());
            assert!(serde_qs::from_str::<MyStruct>(concat!("rw_lock", $rest)).is_err());
        };
    }
    macro_rules! serde_json_eq {
        ($s:literal, $result:expr) => {
            let a: MyStruct = serde_json::from_str($s).unwrap();
            assert_eq!(a.cell, Cell::new($result));
            assert_eq!(a.ref_cell, RefCell::new($result));
            assert_eq!(*a.mutex.lock().unwrap(), $result);
            assert_eq!(*a.rw_lock.read().unwrap(), $result);
        };
    }
    macro_rules! serde_json_err {
        ($v:tt) => {
            assert!(serde_json::from_str::<MyStruct>(r#" { "cell": $v } "#).is_err());
            assert!(serde_json::from_str::<MyStruct>(r#" { "ref_cell": $v } "#).is_err());
            assert!(serde_json::from_str::<MyStruct>(r#" { "mutex": $v } "#).is_err());
            assert!(serde_json::from_str::<MyStruct>(r#" { "rw_lock": $v } "#).is_err());
        };
    }
    #[test]
    fn test_deserialize_wrap_option_number_from_string() {
        serde_qs_eq!("cell=1&ref_cell=1&mutex=1&rw_lock=1", Some(1.0));
        serde_qs_eq!("cell=-1&ref_cell=-1&mutex=-1&rw_lock=-1", Some(-1.0));
        serde_qs_eq!("cell=0.1&ref_cell=0.1&mutex=0.1&rw_lock=0.1", Some(0.1));
        serde_qs_eq!(
            "cell=-0.1&ref_cell=-0.1&mutex=-0.1&rw_lock=-0.1",
            Some(-0.1)
        );
        serde_qs_eq!("cell=&ref_cell=&mutex=&rw_lock=", None);
        serde_qs_eq!("cell&ref_cell&mutex&rw_lock", None);

        serde_qs_err!("=true");
        serde_qs_err!("=a");
        serde_qs_err!("[a]=");
        serde_qs_err!("[]=");

        serde_json_eq!(
            r#" { "cell":"1","ref_cell":"1","mutex":"1","rw_lock":"1" } "#,
            Some(1.0)
        );
        serde_json_eq!(
            r#" { "cell":"-1","ref_cell":"-1","mutex":"-1","rw_lock":"-1" } "#,
            Some(-1.0)
        );
        serde_json_eq!(
            r#" { "cell":"0.1","ref_cell":"0.1","mutex":"0.1","rw_lock":"0.1" } "#,
            Some(0.1)
        );
        serde_json_eq!(
            r#" { "cell":"-0.1","ref_cell":"-0.1","mutex":"-0.1","rw_lock":"-0.1" } "#,
            Some(-0.1)
        );
        serde_json_eq!(
            r#" { "cell":1,"ref_cell":1,"mutex":1,"rw_lock":1 } "#,
            Some(1.0)
        );
        serde_json_eq!(
            r#" { "cell":-1,"ref_cell":-1,"mutex":-1,"rw_lock":-1 } "#,
            Some(-1.0)
        );
        serde_json_eq!(
            r#" { "cell":0.1,"ref_cell":0.1,"mutex":0.1,"rw_lock":0.1 } "#,
            Some(0.1)
        );
        serde_json_eq!(
            r#" { "cell":-0.1,"ref_cell":-0.1,"mutex":-0.1,"rw_lock":-0.1 } "#,
            Some(-0.1)
        );
        serde_json_eq!(
            r#" { "cell":"","ref_cell":"","mutex":"","rw_lock":"" } "#,
            None
        );
        serde_json_eq!(
            r#" { "cell":null,"ref_cell":null,"mutex":null,"rw_lock":null } "#,
            None
        );

        serde_json_err!(true);
        serde_json_err!("a");
        serde_json_err!({});
        serde_json_err!([]);
    }

    #[derive(Debug, serde::Deserialize)]
    struct TestStruct {
        #[serde(default, deserialize_with = "deserialize_option_number_from_string")]
        value: Option<f32>,
    }

    #[test]
    fn deserialize_string_variant_valid_number() {
        let json = r#"{"value": "4\u0032.5"}"#;
        let result: TestStruct = serde_json::from_str(json).unwrap();
        assert_eq!(result.value, Some(42.5));
    }
}
