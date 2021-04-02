use std::fmt::Display;
use std::str::FromStr;

use serde::{Deserialize, Deserializer};

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
/// fn main() {
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
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_number_from_string")]
///     number_from_string: u64,
/// }
/// fn main() {
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
/// use std::str::FromStr;
/// use std::num::{ParseIntError, ParseFloatError};
///
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]
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
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
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

/// Deserializes an option number from string or a number.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(Debug, serde::Deserialize)]
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
/// fn main() {
///     serde_qs_eq("option_num=1", Some(1.0));
///     serde_qs_eq("option_num=-1", Some(-1.0));
///     serde_qs_eq("option_num=0.1", Some(0.1));
///     serde_qs_eq("option_num=-0.1", Some(-0.1));
///     serde_qs_eq("option_num=", None);
///     serde_qs_eq("option_num", None);
///
///     serde_qs_err("option_num=true");
///     serde_qs_err("option_num=a");
///     serde_qs_err("option_num[a]=");
///     serde_qs_err("option_num[]=");
///
///     serde_json_eq(r#" { "option_num": "1" } "#, Some(1.0));
///     serde_json_eq(r#" { "option_num": "-1" } "#, Some(-1.0));
///     serde_json_eq(r#" { "option_num": "0.1" } "#, Some(0.1));
///     serde_json_eq(r#" { "option_num": "-0.1" } "#, Some(-0.1));
///     serde_json_eq(r#" { "option_num": 1 } "#, Some(1.0));
///     serde_json_eq(r#" { "option_num": -1 } "#, Some(-1.0));
///     serde_json_eq(r#" { "option_num": 0.1 } "#, Some(0.1));
///     serde_json_eq(r#" { "option_num": -0.1 } "#, Some(-0.1));
///     serde_json_eq(r#" { "option_num": "" } "#, None);
///     serde_json_eq(r#" { "option_num": null } "#, None);
///
///     serde_json_err(r#" { "option_num": true } "#);
///     serde_json_err(r#" { "option_num": "a" } "#);
///     serde_json_err(r#" { "option_num": {} } "#);
///     serde_json_err(r#" { "option_num": [] } "#);
/// }
/// ```
pub fn deserialize_option_number_from_string<'de, T, D>(
    deserializer: D,
) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: FromStr + serde::Deserialize<'de>,
    <T as FromStr>::Err: Display,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum NumericOrNull<'a, T> {
        Str(&'a str),
        FromStr(T),
        Null,
    }

    match NumericOrNull::<T>::deserialize(deserializer)? {
        NumericOrNull::Str(s) => match s {
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
            T: FromStr + serde::Deserialize<'de>,
            <T as FromStr>::Err: Display,
        {
            #[derive(Deserialize)]
            #[serde(untagged)]
            enum NumericOrNull<'a, T> {
                Str(&'a str),
                FromStr(T),
                Null,
            }

            match NumericOrNull::<T>::deserialize(deserializer)? {
                NumericOrNull::Str(s) => match s {
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
    /// #[derive(Debug, serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(deserialize_with = "deserialize_cell_option_number_from_string")]
    ///     v: Cell<Option<f32>>
    /// }
    /// fn main() {
    ///     let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    ///     assert_eq!(a.v, Cell::new(Some(-0.1)));
    /// }
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
    /// #[derive(Debug, serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_ref_cell_option_number_from_string")]
    ///     v: RefCell<Option<f32>>
    /// }
    /// fn main() {
    ///     let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    ///     assert_eq!(a.v, RefCell::new(Some(-0.1)));
    /// }
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
    /// #[derive(Debug, serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_mutex_option_number_from_string")]
    ///     v: Mutex<Option<f32>>
    /// }
    /// fn main() {
    ///     let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    ///     assert_eq!(*a.v.lock().unwrap(), Some(-0.1));
    /// }
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
    /// #[derive(Debug, serde::Deserialize)]
    /// struct MyStruct {
    ///     #[serde(default, deserialize_with = "deserialize_rw_lock_option_number_from_string")]
    ///     v: RwLock<Option<f32>>
    /// }
    /// fn main() {
    ///     let a = serde_qs::from_str::<MyStruct>("v=-0.1").unwrap();
    ///     assert_eq!(*a.v.read().unwrap(), Some(-0.1));
    /// }
    /// ```
    deserialize_rw_lock_option_number_from_string,
    std::sync::RwLock<Option<T>>
);

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
}

/// Deserializes boolean from anything (string, number, boolean). If input is a string,
/// it is expected, that it is possible to convert it to a number. The return boolean is
/// `true` if the number was either `1` or `1.0` after parsing.
///
/// # Example
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
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

/// Deserializes string from a number. If the original value is a number value,
/// it will be converted to a string.
///
/// # Example:
///
/// ```rust
/// use serde_aux::prelude::*;
///
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_string_from_number")]
///     number_as_string: String,
/// }
/// fn main() {
///     let s = r#" { "number_as_string": "foo" } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_as_string, "foo");
///
///     let s = r#" { "number_as_string": -13 } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_as_string, "-13");
///
///     let s = r#" { "number_as_string": 24.0034 } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.number_as_string, "24.0034");
/// }
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
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_default_from_null")]
///     null_as_default: u64,
/// }
///
/// fn main() {
///     let s = r#" { "null_as_default": 42 } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.null_as_default, 42);
///
///     let s = r#" { "null_as_default": null } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.null_as_default, 0);
///
///     let s = r#" { "null_as_default": "wrong_type" } "#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// }
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
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_default_from_empty_object")]
///     empty_as_default: Option<MyInnerStruct>,
/// }
///
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyInnerStruct {
///     mandatory: u64,
/// }
///
/// fn main() {
///     let s = r#" { "empty_as_default": { "mandatory": 42 } } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(a.empty_as_default.unwrap().mandatory, 42);
///
///     let s = r#" { "empty_as_default": null } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.empty_as_default.is_none());
///
///     let s = r#" { "empty_as_default": {} } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert!(a.empty_as_default.is_none());
///
///     let s = r#" { "empty_as_default": { "unknown": 42 } } "#;
///     assert!(serde_json::from_str::<MyStruct>(s).is_err());
/// }
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
/// #[derive(serde::Serialize, serde::Deserialize, Debug)]
/// struct MyStruct {
///     #[serde(deserialize_with = "deserialize_vec_from_string_or_vec")]
///     list: Vec<i32>,
/// }
///
/// fn main() {
///     let s = r#" { "list": "1,2,3,4" } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(&a.list, &[1, 2, 3, 4]);
///
///     let s = r#" { "list": [1,2,3,4] } "#;
///     let a: MyStruct = serde_json::from_str(s).unwrap();
///     assert_eq!(&a.list, &[1, 2, 3, 4]);
/// }
/// ```
pub fn deserialize_vec_from_string_or_vec<'de, T, D>(deserializer: D) -> Result<Vec<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: FromStr + serde::Deserialize<'de>,
    <T as FromStr>::Err: std::fmt::Display,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum StringOrVec<T> {
        String(String),
        Vec(Vec<T>),
    }

    match StringOrVec::<T>::deserialize(deserializer)? {
        StringOrVec::String(s) => s
            .split(",")
            .map(T::from_str)
            .collect::<Result<Vec<_>, _>>()
            .map_err(serde::de::Error::custom),
        StringOrVec::Vec(v) => Ok(v),
    }
}
