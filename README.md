# SQL derivative sensitivity analysis tool

## Prerequisites

To set up SQL derivative sensitivity analysis tool, you need to install:

1) GHC version 8.0.2 (`sudo apt-get install ghc`)

2) Cabal-install version 1.24.2.0 (`sudo apt-get install cabal-install`)

3) Libpq-dev version 10.10 (`sudo apt-get install libpq-dev`)

4) Postgresql version 10 (`sudo apt install postgresql postgresql-contrib`)

5) Postgresql-contrib version 10 (`sudo apt install postgresql postgresql-contrib`)

## Building

# Using build script

The easiest way to build the tool is to run

`sh build.sh`

from 'banach' directory. Some warnings may come while building 'BanachQ.hs', which is fine.

# Build step by step

Alternatively, the analyser can be built step by step, running the following commands from 'banach' directory.

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

If PostgreSQL has not been installed yet, it needs to be done before running. The analyser has been tested with versions from 9.5.13 to 10. After PostgreSQL has been installed, it is necessary to create a database named 'banach'.
Permissions on 'banach' database need to be given to the user USERNAME that will run the analyser:

# Using configuration script

The easiest way to create the database is using a script. The script will however require superuser rights.

`sudo -u postgres -i psql -f configure_psql.sql -v u=USERNAME`

# Configure step by step

Alternatively, the user and the database can be set up step by step. Here is an example of how to do it with Ubuntu system:

    USERNAME@xxxx:~$ sudo -u postgres -i
    (prompts USERNAME's password)
    postgres@xxxx:~$ psql
    postgres=# create user USERNAME;
    postgres=# create database USERNAME;
    postgres=# \q

Now try to log in under USERNAME:

    postgres@xxxx:~$ exit
    logout
    USERNAME@xxxx:~$ psql
    psql (9.5.13)
    Type "help" for help.

Finally, create the database named 'banach'

    USERNAME=# create database banach;
    CREATE DATABASE
    USERNAME=# \c banach;
    You are now connected to database "banach" as user USERNAME.
    USERNAME=# \q

All required components should now have been installed and configured.

## Testing

The test examples can be run as

`sh run_tests.sh`

These tests just run some example queries and compare the obtained output with a fixed pre-computed output. There are no unit test or quick check tests, and the analyser can be currently tested only manually.

## Examples:

Derivative sensitivity analysis can be run from 'banach' directory as follows:

   dist/build/banach/banach -QD --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --epsilon 1.0 --beta 0.1

where
    - demo_schema.sql contains the database schema
    - demo_query.sql contains the query
    - demo_constraints.att (allowed to be an empty file) is the description of constraints on attributes
    - epsilon is the level of differential privacy that we want to achieve
    The parameter beta is only related to optimization and is optional.

If you want the analyzer to be less verbose and only display relevant output, use the parameter 's':

  dist/build/banach/banach -QDs --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --epsilon 1.0 --beta 0.1

More examples can be found in the subdirectories of 'lightweight-examples', where 'demo.sh' scripts show how to run these examples.

The parameter --db-create-tables reads data from .db files and stores it to PostgreSQL database. Hence, if the data has already been uploaded once and it has not been updated, there is no need to create the tables again, and --db-create-tables can be removed.

