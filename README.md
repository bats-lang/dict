# dict

Hash map (dictionary) for the [Bats](https://github.com/bats-lang) programming language.

## Features

- Mutable dictionary with linear ownership (`dict(k, v)`)
- Frozen (immutable) dictionary (`frozen_dict(k, v)`)
- Insert, lookup, remove, iterate
- Generic over key and value types

## Usage

```bats
#use dict as D

val d = $D.create<int><string>()
val () = $D.insert<int><string>(d, 42, "hello")
val v = $D.lookup<int><string>(d, 42)
```

## API

See [docs/lib.md](docs/lib.md) for the full API reference.
