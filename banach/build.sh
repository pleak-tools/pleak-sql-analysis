cabal sandbox init
cabal update
cabal install --only-dependencies
cabal configure
cabal build
sh run_tests.sh
