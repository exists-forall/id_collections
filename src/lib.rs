//! Index-oriented programming in Rust.
//!
//! It is common in Rust to define custom wrapper types (sometimes called ["newtypes"](
//! https://doc.rust-lang.org/rust-by-example/generics/new_types.html)) around integer types, in
//! order to better communicate the intended meaning of those types, and to catch mistakes arising
//! from mixing up integer values with different meanings. For example, one might define two
//! different types representing "user ids" and "group ids":
//!
//! ```
//! struct UserId(u32);
//! struct GroupId(u32);
//! ```
//!
//! The `id_collections` crate provides data structures designed to work with these kinds of
//! strongly-typed wrappers around integer types:
//! - The [`IdVec<I, T>`] type is a vector which uses a custom index type `I` instead of [`usize`].
//! - The [`IdMap<I, T>`] type is a map backed by a vector. It's similar to [`IdVec<I, T>`], except
//!   that its set of keys is not required to occupy a contiguous range, so you can fill in its
//!   entries out of order.
//! - The [`Count<I>`] type provides a type-safe way to represent the size of a range of custom ids.
//!
//! To use the structures in this library with your application's id types, your id types need to
//! implement the [`Id`] trait. The easiest way to implement the [`Id`] trait is to use the
//! [`#[id_type]`](macro@id_type) attribute macro:
//!
//! ```
//! use id_collections::id_type;
//!
//! #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! struct UserId(u32);
//!
//! #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! struct GroupId(u32);
//! ```
//!
//! After you've implemented [`Id`], you can use your custom id type as the index type for an
//! [`IdVec`]:
//!
//! ```
//! # use id_collections::id_type;
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct UserId(u32);
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct GroupId(u32);
//! #
//! use id_collections::IdVec;
//!
//! let mut users: IdVec<UserId, &str> = IdVec::new();
//! let alice_id: UserId = users.push("Alice");
//! let bob_id: UserId = users.push("Bob");
//!
//! assert_eq!(users[alice_id], "Alice");
//! assert_eq!(users[bob_id], "Bob");
//! ```
//!
//! Using [`IdVec`] prevents you from accidentally mixing up different id types:
//!
//! ```compile_fail
//! # use id_collections::id_type;
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct UserId(u32);
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct GroupId(u32);
//! #
//! # use id_collections::IdVec;
//! #
//! # let mut users: IdVec<UserId, &str> = IdVec::new();
//! #
//! let group = GroupId(1);
//! let name = users[group]; // error: expected 'UserId', found 'GroupId'!
//! ```
//!
//! If you need a collection which supports discontiguous keys, you can use [`IdMap`]:
//!
//! ```
//! # use id_collections::id_type;
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct UserId(u32);
//! #
//! # #[id_type]
//! # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
//! # struct GroupId(u32);
//! #
//! use id_collections::IdMap;
//!
//! let mut users: IdMap<UserId, &str> = IdMap::new();
//! users.insert(UserId(5), "Alice");
//! users.insert(UserId(10), "Bob");
//! assert_eq!(users[UserId(5)], "Alice");
//! assert_eq!(users[UserId(10)], "Bob");
//! ```

pub mod count;
pub mod id;
pub mod id_map;
pub mod id_vec;

#[doc(inline)]
pub use count::Count;

#[doc(inline)]
pub use id::Id;

/// Easily define custom [`Id`] types.
///
/// You can use the `#[id_type]` attribute macro on any struct type which wraps an unsigned integer.
/// The `#[id_type]` macro will automatically derive the [`Id`](trait@Id) trait for that struct
/// type, and will also derive all the standard library traits which the [`Id`](trait@Id) trait
/// requires, as well as the [`Debug`](std::fmt::Debug) trait:
/// ```
/// use id_collections::{Id, id_type};
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct UserId(u32);
///
/// // 'UserId' implements 'Id', as well as 'Eq', 'Ord', etc.:
/// assert_eq!(UserId(10).to_index(), 10);
/// assert_eq!(UserId::from_index(10), UserId(10));
/// assert!(UserId(10) < UserId(20));
///
/// // 'UserId' implements 'Debug':
/// println!("{:?}", UserId(10));
/// ```
///
/// You can use the `#[id_type]` macro on both tuple-style structs and on structs with named fields,
/// as long as they have only a single field containing an unsigned integer:
/// ```
/// use id_collections::id_type;
///
/// // Okay:
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct FooId(u32);
///
/// // Also okay:
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct BarId {
///     index: u32,
/// }
/// ```
///
/// # Options for Deriving [`Debug`](std::fmt::Debug)
///
/// By default, the `#[id_type]` macro will derive the [`Debug`](std::fmt::Debug) trait for your
/// struct type. The behavior of the macro regarding the [`Debug`](std::fmt::Debug) trait can be
/// configured with the `debug=...` option, which accepts the following values:
///
/// | Option | Effect |
/// | ------ | ------ |
/// | `debug=false` | Don't derive [`Debug`](std::fmt::Debug). |
/// | `debug="standard"` | Derive [`Debug`](std::fmt::Debug) using the standard `#[derive(Debug)]` mechanism built-in to Rust.
/// | `debug="compact"` | Derive [`Debug`](std::fmt::Debug) using a custom implementation which generates less whitespace when pretty-printing than you would get by using `#[derive(Debug)]`. |
///
/// The default is **`debug="compact"`**.
///
/// ```
/// use id_collections::id_type;
///
/// // 'FirstId' does not implement 'Debug':
/// #[id_type(debug = false)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct FirstId(u32);
///
/// // 'SecondId' implements 'Debug' as if we had written '#[derive(Debug)]':
/// #[id_type(debug = "standard")]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct SecondId(u32);
///
/// // The "standard" 'Debug' implementation generates a large amount of whitespace when
/// // pretty-printing with '#?':
/// let second_expected = "\
/// SecondId(
///     10,
/// )";
/// assert_eq!(&format!("{:#?}", SecondId(10)), second_expected);
///
/// // 'ThirdId' implements 'Debug' using an implementation which generates less whitespace:
/// #[id_type(debug = "compact")]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct ThirdId(u32);
/// assert_eq!(&format!("{:#?}", ThirdId(10)), "ThirdId(10)");
///
/// // The default is equivalent to 'debug="compact"':
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct FourthId(u32);
/// assert_eq!(&format!("{:#?}", FourthId(10)), "FourthId(10)");
/// ```
///
/// # Deriving Serde Traits
///
/// By default, the `#[id_type]` macro does not derive `serde::Serialize` or `serde::Deserialize`.
/// For convenience, you can enable deriving these traits by passing the option `serde = true` to
/// the macro, which is shorter than writing `#[derive(Serialize, Deserialize)]` manually:
///
/// ```
/// # #[cfg(feature = "serde")]
/// # {
/// use id_collections::id_type;
///
/// #[id_type(serde = true)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct UserId(u32);
///
/// /* the above is equivalent to:
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// #[derive(serde::Serialize, serde::Deserialize)]
/// struct UserId(u32);
///
/// */
/// # }
/// ```
#[doc(inline)]
pub use id_collections_derive::id_type;

/// Derive [`Id`] for custom types.
///
/// You can derive [`Id`] for any struct type which wraps an unsigned integer type. Deriving [`Id`]
/// works for both tuple-style structs, and structs with named fields, as long as they have only a
/// single field containing an unsigned integer:
///
/// ```
/// use id_collections::Id;
///
/// // Okay:
/// #[derive(Id, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct FooId(u32);
///
/// // Also okay:
/// #[derive(Id, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct BarId {
///     index: u32,
/// }
/// ```
///
/// Rather than explicitly deriving [`Id`] and all the standard library traits which it requires, it
/// is usually more convenient to use the [`#[id_type]`](macro@id_type) attribute macro to define
/// custom [`Id`] types.
#[doc(inline)]
pub use id_collections_derive::Id;

#[doc(inline)]
pub use id_map::IdMap;

#[doc(inline)]
pub use id_vec::IdVec;

#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn test_derive_id_tuple_struct() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Id)]
        struct TestId(u32);

        assert_eq!(TestId::from_index(10u32), TestId(10));
        assert_eq!(TestId(10).to_index(), 10u32);
    }

    #[test]
    fn test_derive_id_named_struct() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Id)]
        struct TestId {
            value: u32,
        }

        assert_eq!(TestId::from_index(10u32), TestId { value: 10 });
        assert_eq!(TestId { value: 10 }.to_index(), 10u32);
    }

    #[test]
    fn test_id_type_macro_tuple_struct() {
        #[id_type]
        struct TestId(u32);

        assert_eq!(TestId::from_index(10u32), TestId(10));
        assert_eq!(TestId(10).to_index(), 10u32);
    }

    #[test]
    fn test_id_type_macro_tuple_struct_debug() {
        #[id_type]
        struct TestId(u32);

        assert_eq!(format!("{:#?}", TestId(10)), "TestId(10)");
    }

    #[test]
    fn test_id_type_macro_tuple_struct_debug_explicit() {
        #[id_type(debug = "compact")]
        struct TestId(u32);

        assert_eq!(format!("{:#?}", TestId(10)), "TestId(10)");
    }

    #[test]
    fn test_id_type_macro_tuple_struct_debug_standard() {
        #[id_type(debug = "standard")]
        struct TestId(u32);

        assert_eq!(format!("{:#?}", TestId(10)), "TestId(\n    10,\n)");
    }

    #[test]
    fn test_id_type_macro_tuple_struct_debug_disable() {
        #[id_type(debug = false)]
        struct TestId(u32);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_id_type_macro_tuple_struct_serde() {
        #[id_type(serde = true)]
        struct TestId(u32);

        let serialized = serde_json::to_string(&TestId(10)).unwrap();
        assert_eq!(serialized, "10");

        let deserialized: TestId = serde_json::from_str("10").unwrap();
        assert_eq!(deserialized, TestId(10));
    }

    #[test]
    fn test_id_type_macro_named_struct() {
        #[id_type]
        struct TestId {
            value: u32,
        }

        assert_eq!(TestId::from_index(10u32), TestId { value: 10 });
        assert_eq!(TestId { value: 10 }.to_index(), 10u32);
    }

    #[test]
    fn test_id_type_macro_named_struct_debug() {
        #[id_type]
        struct TestId {
            value: u32,
        }

        assert_eq!(
            format!("{:#?}", TestId { value: 10 }),
            "TestId { value: 10 }"
        );
    }

    #[test]
    fn test_id_type_macro_named_struct_explicit() {
        #[id_type(debug = "compact")]
        struct TestId {
            value: u32,
        }

        assert_eq!(
            format!("{:#?}", TestId { value: 10 }),
            "TestId { value: 10 }"
        );
    }

    #[test]
    fn test_id_type_macro_named_struct_debug_standard() {
        #[id_type(debug = "standard")]
        struct TestId {
            value: u32,
        }

        assert_eq!(
            format!("{:#?}", TestId { value: 10 }),
            "TestId {\n    value: 10,\n}"
        );
    }

    #[test]
    fn test_id_type_macro_named_struct_debug_disable() {
        #[id_type(debug = false)]
        struct TestId {
            value: u32,
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_id_type_macro_named_struct_serde() {
        #[id_type(serde = true)]
        struct TestId {
            value: u32,
        }

        let serialized = serde_json::to_string(&TestId { value: 10 }).unwrap();
        assert_eq!(serialized, r#"{"value":10}"#);

        let deserialized: TestId = serde_json::from_str(r#"{"value":10}"#).unwrap();
        assert_eq!(deserialized, TestId { value: 10 });
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_id_type_macro_named_struct_serde_transparent() {
        #[id_type(serde = true)]
        #[serde(transparent)]
        struct TestId {
            value: u32,
        }

        let serialized = serde_json::to_string(&TestId { value: 10 }).unwrap();
        assert_eq!(serialized, "10");

        let deserialized: TestId = serde_json::from_str("10").unwrap();
        assert_eq!(deserialized, TestId { value: 10 });
    }

    #[test]
    fn readme_example() {
        use crate::{id_type, IdMap, IdVec};

        #[id_type]
        struct FileId(usize);

        #[id_type]
        struct DirectoryId(usize);

        #[derive(Default)]
        struct DirectoryContents {
            files: Vec<FileId>,
            subdirectories: Vec<DirectoryId>,
        }

        /// Calculate the size of each directory in `directories`.
        ///
        /// `directories` may contain file and directory "hard links" (i.e., a file or directory may
        /// be pointed to by multiple parent directories), but for simplicity we assume that the
        /// filesystem may not contain cycles (i.e., a directory is not allowed to directly or
        /// indirectly contain itself).
        fn calculate_sizes(
            file_sizes: &IdVec<FileId, u64>,
            directories: &IdVec<DirectoryId, DirectoryContents>,
        ) -> IdVec<DirectoryId, u64> {
            fn calculate_size_rec(
                file_sizes: &IdVec<FileId, u64>,
                directories: &IdVec<DirectoryId, DirectoryContents>,
                directory_sizes: &mut IdMap<DirectoryId, u64>,
                directory: DirectoryId,
            ) -> u64 {
                if let Some(&cached_size) = directory_sizes.get(directory) {
                    return cached_size;
                }

                let mut size = 0;
                for file in &directories[directory].files {
                    size += file_sizes[file];
                }
                for &subdirectory in &directories[directory].subdirectories {
                    size +=
                        calculate_size_rec(file_sizes, directories, directory_sizes, subdirectory);
                }
                directory_sizes.insert_vacant(directory, size);
                size
            }

            let mut directory_sizes = IdMap::with_capacity(directories.len());
            for directory in directories.count() {
                calculate_size_rec(file_sizes, directories, &mut directory_sizes, directory);
            }

            directory_sizes.to_id_vec(directories.count())
        }

        let mut file_sizes = IdVec::new();
        let mut directories: IdVec<_, DirectoryContents> = IdVec::new();

        let file_1 = file_sizes.push(3);
        let file_2 = file_sizes.push(5);
        let dir_1 = directories.push(Default::default());
        let dir_2 = directories.push(Default::default());
        let dir_3 = directories.push(Default::default());

        directories[dir_3].files.push(file_1);
        directories[dir_1].files.push(file_2);

        directories[dir_1].subdirectories.push(dir_2);
        directories[dir_1].subdirectories.push(dir_3);
        directories[dir_2].subdirectories.push(dir_3);

        let sizes = calculate_sizes(&file_sizes, &directories);
        assert_eq!(sizes.count(), directories.count());
        assert_eq!(sizes[dir_1], 11);
        assert_eq!(sizes[dir_2], 3);
        assert_eq!(sizes[dir_3], 3);
    }
}
