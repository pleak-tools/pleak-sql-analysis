# SQL analysis tools for pleak.io

This repository contains three different analysers:

1) [SQL global sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/globalsensitivity-cabal)

2) [SQL local sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/localsensitivity-cabal)

3) [SQL derivative sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/banach)

## Prerequisites

To set up SQL analysis tools, you need to install:

1) Postgresql - `sudo apt install postgresql postgresql-contrib`

2) Libpq - `sudo apt-get install libpq-dev`

3) Cabal-install - `sudo apt-get install cabal-install`

4) GHC - `sudo apt-get install ghc`

5) Z3 Theorem Prover - to install, you can clone it from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) and compile it yourself or (on some Linux versions, for example Ubuntu 16.4) execute `apt install z3`. You will need Z3 to be in the PATH.

## Building & using

All three analysers can be built using cabal. Find specific details in [SQL global sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/globalsensitivity-cabal), [SQL local sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/localsensitivity-cabal) and [SQL derivative sensitivity analysis tool](https://github.com/pleak-tools/pleak-sql-analysis/tree/master/banach) directories.

All three analysers can be used as command-line analysers or with GUI in [Pleak sensitivities editor](https://github.com/pleak-tools/pleak-sensitivities-editors).

## License

The MIT License

Copyright 2015-2020 Cybernetica AS

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
