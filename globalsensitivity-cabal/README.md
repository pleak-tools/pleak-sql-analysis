# SQL global sensitivity analysis tool for pleak.io

Building for the first time:

`cabal sandbox init`

`cabal update`

`cabal install happy`

`cabal install --only-dependencies`

`cabal configure`

`cabal build`

Later, only 
`cabal build` 
is required to rebuild when files have changed.

If dependencies or project structure has changed then

`cabal install --only-dependencies`

`cabal configure`

`cabal build`

may be necessary.

After building, the executable can be run with
    dist/build/sqla/sqla
