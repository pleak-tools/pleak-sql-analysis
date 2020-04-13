# SQL derivative sensitivity analysis tool

Given a database schema, database contents, SQL query with a numeric output (or several numeric outputs), and some epsilon > 0, the tool computes the amount of noise that needs to be added to the output to make it epsilon-differentially private. The computation of noise magnitude is based on 'derivative sensitivity' of a query, which is an instance of 'smooth local sensitivity', and hence needs actual data to compute the noise magnitude.

This repository contains a frozen branch of derivative sensitivity analysis tool, which has been used to perform the experiments for the paper "A Framework of Metrics for Differential Privacy from Local Sensitivity" (located at https://petsymposium.org/2020/files/papers/issue2/popets-2020-0023.pdf). This paper describes theory behind the analysis. Contemporary version of the tool (whcih includes several other tools) can be found in the master branch of https://github.com/pleak-tools/pleak-sql-analysis.

## Description

The analyzer starts running from `Main.hs`. The analysis runs in three main phases.

- `PreprocessQ.hs` reads in the query and prepares it for analysis. It transforms the query to its continuous approximation (e.g. replaces filters with sigmoids). It makes the table norms described in `.nrm` files compatible with the query.

- `Banach.hs` and `BanachQ.hs` is the main engine that actually computes the sensitivity of a continuous function on a database.

- `PostprocessQ.hs` optionally calls BanachQ.hs several times to get a solution with optimal smoothness beta (if it had not been fixed in advance). It converts the sensitivity computed by BanachQ.hs to more interpretable metrics (like absolute and relative errors).

These main modules in turn are using various other helpful modules:

* `AExprQ.hs` - describes an arithmetic expression, into which the SELECT-statement of a query is transformed after parsing. 
* `CreateTablesQ.hs` - uploads table data from provided `.db` files to PSQL database (if --db-create-tables parameter is set)
* `DatabaseQ.hs` - functionalities for interacting with PSQL database (read and insert data).
* `ErrorMsg.hs` - lists all error messages that are output for different error cases found in the other modules.
* `ExprQ.hs` - describes the input SQL query in a special format that can be consumed by the main sensitivity computing engine. The main difference from AExprQ.hs is that it contains only numberical computations, and special markers showing scaling of norms and/or denoting the places where some part of the expression does not have sensitive variables and can be treated as constant. While AExprQ.hs only describes SELECT-statements without aggregations, ExprQ.hs defines aggregations as well.
* `GroupQ.hs` - contains structures that allow to define groups in queries, which is basically just syntactic sugar that splits one query to several queries, one for each possible group.
* `NormsQ.hs` - functionality related to computation of norms, and adjusting the "query norm" to the "database norm".
* `ParserQ.hs` - a parser for additional auxiliary structures like table norm and possible constraints on attributes (used e.g. to determine the groups in a group by query)
* `ProgramOptions.hs` - defines the list of possible program options of the analyzer
* `QueryQ.hs` - describes the query data structure
* `RangeUtils.hs` - contains some computations of ranges of values (used if the ranges are given as additional constraints on attributes). We can get smaller sensitivity if we restrict an input attribute to a smaller set of values.
* `ReaderQ.hs` - reads data from text files before feeding it to parser
* `LoggingQ.hs`, `SchemaQ.hs`, `SelectQueryQ.hs` - parser for SQL queries and schemas, which is based on `hssqlppp` library.


Not relevant for derivative sensitivity artifact:
 - PolicyQ.hs
 - TimeSeriesQ.hs
 - VarstateQ.hs

## Prerequisites

To set up SQL derivative sensitivity analysis tool, you need to install:

1) GHC version 8.0.2 (`sudo apt-get install ghc`)

2) Cabal-install version 1.24.2.0 (`sudo apt-get install cabal-install`)

3) Libpq-dev version 10.10 (`sudo apt-get install libpq-dev`)

4) Postgresql version 10 (`sudo apt install postgresql postgresql-contrib`)

5) Postgresql-contrib version 10 (`sudo apt install postgresql postgresql-contrib`)

## Building

### Using build script

The easiest way to build the tool is to run

`sh build.sh`

from `banach` directory. Some warnings may come while building `BanachQ.hs`, which is fine.

### Build step by step

Alternatively, the analyser can be built step by step, running the following commands from `banach` directory.

Building for the first time:

`cabal sandbox init`

`cabal update`

`cabal install --only-dependencies`

`cabal configure`

`cabal build`

The executable is created in the subdirectory dist/build/banach, thus to execute it:
    dist/build/banach/banach

Later, only 
`cabal build`
is required to rebuild when files have changed.

If dependencies or project structure has changed then

`cabal install --only-dependencies`

`cabal configure`

`cabal build`

may be necessary.

## Configuring

If PostgreSQL has not been installed yet, it needs to be done before running. The analyser has been tested with versions from 9.5.13 to 10. After PostgreSQL has been installed, it is necessary to create a database named `banach`.
Permissions on `banach` database need to be given to the user USERNAME that will run the analyser:

### Using configuration script

The easiest way to create the database is using a script. The script will however require superuser rights.

`sudo -u postgres -i psql -f configure_psql.sql -v u=USERNAME`

### Configure step by step

Alternatively, the user and the database can be set up step by step. Here is an example of how to do it with Ubuntu system:

`
    USERNAME@xxxx:~$ sudo -u postgres -i
    (prompts USERNAME's password)
    postgres@xxxx:~$ psql
    postgres=# create user USERNAME;
    postgres=# create database USERNAME;
    postgres=# \q
`

Now try to log in under USERNAME:

`
    postgres@xxxx:~$ exit
    logout
    USERNAME@xxxx:~$ psql
    psql (9.5.13)
    Type "help" for help.
`

Finally, create the database named `banach`
`
    USERNAME=# create database banach;
    CREATE DATABASE
    USERNAME=# \c banach;
    You are now connected to database "banach" as user USERNAME.
    USERNAME=# \q
`
All required components should now have been installed and configured.

## Testing

The test examples can be run as

`sh run_tests.sh`

These tests just run some example queries and compare the obtained output with a fixed pre-computed output. There are no unit test or quick check tests, and the analyser can be currently tested only manually.

## Examples:

Derivative sensitivity analysis can be run from `banach` directory as follows:

`dist/build/banach/banach -QD --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --epsilon 1.0 --beta 0.1`

where
    - demo_schema.sql contains the database schema
    - demo_query.sql contains the query
    - demo_constraints.att (allowed to be an empty file) is the description of constraints on attributes
    - epsilon is the level of differential privacy that we want to achieve
    The parameter beta is only related to optimization and is optional.

If you want the analyzer to be less verbose and only display relevant output, use the parameter `s`:

`dist/build/banach/banach -QDs --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --epsilon 1.0 --beta 0.1`

The parameter `--db-create-tables` reads data from `.db` files and stores it to PostgreSQL database. Hence, if the data has already been uploaded once and it has not been updated, there is no need to create the tables again, and `--db-create-tables` can be removed.

More examples can be found in the subdirectories of `banach/lightweight-examples`, where `demo.sh` scripts show how to run these examples.

## Additional information

Installation guide and (guides to) lightweight examples can be found at `https://pleak.io/wiki/sql-derivative-sensitivity-analyser_install`. Explanation of input and output format can be found at `https://pleak.io/wiki/sql-derivative-sensitivity-analyser_advanced`.

