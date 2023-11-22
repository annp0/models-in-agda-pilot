## Model: File Systems

Files `File` and directories `Dir`:

```agda
data File : Set where
    file : File

data Dir : Set where
    dir : Dir
```

They are all file system objects `FSObj`:

```agda
data FSObj : Set where
    fromFile : File -> FSObj
    fromDir : Dir -> FSObj
```

File systems `FS`:
```
record FS : Set where {
    live: List FSObj,
    // live is the collection of contained FSObj
    root: Dir ∩ live,
    // the root must be in the intersection of Dir and live
    parent: (live - {root}) -> Dir ∩ live,
    // a function that assigns each live object (except root) a parent
    contents: Dir -> {All subsets of live}
    // a function that assigns each directory with contents
}{
    // Additional constraints
    
    for all x in live, x in root.*contents
    // all elements of live is reachable from root
    for all x in (live - {root}), x in parent(x).contents
    // for all elements of live, it must be in the contents of its parent
}
```

To implement `FS`, I'm thinking about how to represent subsets and removal of an element from a set.

After implementing `FS`, we define two operations:

1. `move`, takes in arguments `a: FS`,  `x` in `a.live`, `d` in `a.live` and `Dir`, and returns a new `FS` with `x` moved into `d`.

2. `remove`, takes in arguments `a: FS`, `x` in `a.live - {a.root}`, and returns a new `FS` with `x` removed.

Then we prove the following properties:

1. For all `a:FS`, there is only one `FSObj` in `a` that does not have a parent, and it is the root.

2. For all `a:FS`, suppose after a move operation with `a` returns `b`, then `a.live` is the same as `b.live`, i.e. they contain the same files

3. For all `a:FS`, and `x` in `a.live - {a.root}`, then `(remove a x).live = a.live - {x.*contents}`, i.e. the files are removed are `x` and its contents.
