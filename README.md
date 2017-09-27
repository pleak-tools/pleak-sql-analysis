# SQL analysis tool for pleak.io

## Prerequisites

To set up the SQL analysis tool, you need:

1) Haskell Tool Stack - to install, execute `wget -qO- https://get.haskellstack.org/ | sh`

2) Z3 Theorem Prover - to install, you can clone it from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) and compile it yourself or (on some Linux versions, for example Ubuntu 16.4) execute `apt install z3`. You will need Z3 to be in the PATH.

## Building

Building is most convenient with stack. Check the project out with git and in the root project directory:

```bash
git submodule init
git submodule update
stack setup
stack build
```
And follow the instructions that stack provides.

## Using

You will need Z3 to be in the PATH. Z3 location can can also be specified with  `--z3-path` flag. See `--help` for more usage information.

Compilation creates a file .sqla into .stack-work/install/x86_64-linux/lts-7.19/8.0.1/bin directory (or some other similarly named directory) that you can link to your root directory by executing `ln -s .stack-work/install/x86_64-linux/lts-7.19/8.0.1/bin/sqla .`. After that, you can:

Execute `./sqla -h` to see different keys.

Execute `./sqla example/schema.sql example/query.sql` to run the analyser on example files.

## Updating

To update the analyser, execute `git pull` and `stack build`.
