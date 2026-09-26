# dict

Hash map (dictionary) for the [Bats](https://github.com/bats-lang) programming language.

## Features

- Mutable dictionary with linear ownership (`dict(k, v)`)
- Frozen (immutable) dictionary (`frozen_dict(k, v)`)
- Insert, lookup, remove; fixed capacity (`insert` returns `false` when full)
- Generic over key and value types; hashing and equality come from
  template implementations the client provides
- Every index is proven by the types: no casts, no runtime range checks

## Usage

```bats
#use array as A
#use dict as D
#use result as R

typedef key = [i:int] int i

implement $D.hash_key<key> (k) = k
implement $D.equal_key<key> (a, b) = a = b

val d = $D.create<key><int>(64)
val ok = $D.insert<key><int>(d, 42, 7)      (* false if the table is full *)
val fd = $D.dict_freeze<key><int>(d)
val v = $D.lookup<key><int>(fd, 42)         (* $R.some(7) *)
```

`#use array` is needed because the dictionary's templates are
instantiated in your program and use array operations.

## Tests

`tests/static/run.sh <repository>` (type-level: accepted and rejected
programs) and `tests/dynamic/run.sh <repository>` (a binary exercising
insert/overwrite/full table/remove/slot reuse/lookup). CI runs both.

## API

See [docs/lib.md](docs/lib.md) for the full API reference.
