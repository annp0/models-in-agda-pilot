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
```agda
record FS : Set where
  {- File Systems -}
  field
    live : List FSObj
    {- The collection of FSObjs contained in this FS -}
    root : Dir
    {- The root of the FS -}
    root-live : (fromDir root) ∈ live
    {- The proof that the root is inside live -}
    parent : (x : FSObj) → x ∈ live → ¬ (x ≡ (fromDir root)) → Dir
    {- For each x in live that is not root, we assign it a parent. -}
    parent-live : (x : FSObj) → (lx : x ∈ live) → (nr : ¬ (x ≡ (fromDir root))) → fromDir (parent x lx nr) ∈ live
    {- The parents assigned must also be inside live -}
    content : (x : Dir) → (fromDir x) ∈ live → (FSObj → Bool)
    {- For each directory inside live, we assign them a collection of FSObjs as its content. -}
    parent-content : (x : FSObj) → (lx : x ∈ live) → (nr : ¬ (x ≡ (fromDir root))) → content (parent x lx nr) (parent-live x lx nr) x ≡ true
    {- For all elements of live, it must be in the contents of its parent. -}

    {-
    reachable-from-root : ?
    For all elements of live, it must be reachable from root (be root itself, or be in the contents of root, or be in the contents of contents of root, and so on)
    still thinking of how to implement
    -}
```

After implementing `FS`, we define two operations:

1. `move`, takes in arguments `a: FS`,  `x` in `a.live`, `d` in `a.live` and `Dir`, and returns a new `FS` with `x` moved into `d`.

2. `remove`, takes in arguments `a: FS`, `x` in `a.live - {a.root}`, and returns a new `FS` with `x` removed.

Then we prove the following properties:

1. For all `a:FS`, there is only one `FSObj` in `a` that does not have a parent, and it is the root.

2. For all `a:FS`, suppose after a move operation with `a` returns `b`, then `a.live` is the same as `b.live`, i.e. they contain the same files

3. For all `a:FS`, and `x` in `a.live - {a.root}`, then `(remove a x).live = a.live - {x.*contents}`, i.e. the files are removed are `x` and its contents.
