# Guide

Chumsky's guide is intended to be viewed through [docs.rs](https://docs.rs/chumsky/latest/chumsky/guide/index.html).

## For contributors

When modifying the guide, please remember to test the docs via rustdoc. You can do this via this command:

```
RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features
```

Appending `--open` will cause the docs to open in your web browser when built.
