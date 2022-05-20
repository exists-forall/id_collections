# `id_collections`: Index-Oriented Programming in Rust

In some Rust applications, one defines custom wrapper types (sometimes called ["newtypes"](https://doc.rust-lang.org/rust-by-example/generics/new_types.html)) around integer types, in order to better communicate intent and to catch mistakes related to mixing up integer values with different meanings. For example, one might define two different types representing "user ids" and "group ids":

```rust
struct UserId(u32);
struct GroupId(u32);
```

The `id_collections` crate provides data structures designed to work with these kinds of strongly-typed wrappers around integer types:
- The `IdVec<I, T>` type is a vector which uses a custom index type `I` instead of `usize`.
- The `IdMap<I, T>` type is a map backed by a vector. It's similar to `IdVec<I, T>`, except that its set of keys is not required to occupy a contiguous range, so you can fill in its entries out of order.
- The `Count<I>` type provides a type-safe way to represent the size of a range of custom ids.

To use the structures in this library with your application's id types, your id types need to implement the `Id` trait. The easiest way to implement the `Id` trait is to use the `#[id_type]` attribute macro:

```rust
use id_collections::id_type;

#[id_type]
struct UserId(u32);

#[id_type]
struct GroupId(u32);
```

After you've implemented `Id`, you can use your custom id type as the index type for an `IdVec`:

```rust
use id_collections::IdVec;

let mut users: IdVec<UserId, &str> = IdVec::new();
let alice_id: UserId = users.push("Alice");
let bob_id: UserId = users.push("Bob");

assert_eq!(users[alice_id], "Alice");
assert_eq!(users[bob_id], "Bob");
```

Using `IdVec` prevents you from accidentally mixing up different id types:

```rust
let group = GroupId(1);
let name = users[group]; // error: expected 'UserId', found 'GroupId'!
```

If you need a collection which supports discontiguous keys, you can use `IdMap`:

```rust
use id_collections::IdMap;

let mut users: IdMap<UserId, &str> = IdMap::new();
users.insert(UserId(5), "Alice");
users.insert(UserId(10), "Bob");
assert_eq!(users[UserId(5)], "Alice");
assert_eq!(users[UserId(10)], "Bob");
```

## Example: Calculating Directory Sizes

One of the main motivating use cases for the `id_collections` crate is to implement graph algorithms. The following example shows how `IdVec`, `IdMap`, and `Count` can be used together to implement a simple depth-first graph traversal which computes the size of each directory in an in-memory representation of a filesystem:

```rust
use id_collections::{id_type, IdMap, IdVec};

#[id_type]
struct FileId(usize);

#[id_type]
struct DirectoryId(usize);

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
```
