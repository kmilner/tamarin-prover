# tamarin-prover (Rust port)

In-progress Rust port of the [Tamarin Prover](https://tamarin-prover.github.io/).
The Haskell sources under `../lib/` and `../src/` remain authoritative during
the transition; this workspace ports them package-by-package in dependency
order:

```
utils → term → theory → {sapic, accountability} → export → tamarin-prover
```

## Build

```
cargo build
cargo test
```
