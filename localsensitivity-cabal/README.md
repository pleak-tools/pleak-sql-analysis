# SQL local sensitivity analysis tool for pleak.io

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

After executing previous commands, go to pleak-sql-analysis/banach directory and execute:
    `chmod a+x sqlsa-quiet`

The executable file will be called by an external derivative sensitivity analyser from catalogue 'banach', so we do not provide direct running instructions here.
