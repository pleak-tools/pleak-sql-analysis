# SQL analysis tool for pleak.io

## Building

Building is most convenient with stack. Check the project out with git and in
the root project directory:

```bash
git submodule init
git submodule update
stack build
```

And follow the instructions that stack provides.

## Using

You will need Z3 to be in the PATH. Z3 location can can also be specified with  `--z3-path` flag. See `--help` for more usage information.

## TODO

- [x] Write `README.md`
- [x] Very basic analysis support
- [ ] Support ALL queries (currently only DISTINCT is supported)
