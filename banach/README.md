# SQL derivative sensitivity analysis tool for pleak.io

## Prerequisites

To set up SQL derivative sensitivity analysis tool, you need to install:

1) Postgresql - `sudo apt install postgresql postgresql-contrib`

2) Libpq - `sudo apt-get install libpq-dev`

3) Cabal-install - `sudo apt-get install cabal-install`

4) GHC - `sudo apt-get install ghc`

## Building

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


If PostgreSQL has not been installed yet, it needs to be done before running. The analyser has been tested with versions from 9.5.13 to 10.

After PostgreSQL has been installed, it is necessary to create a database named 'banach'.
Permissions on 'banach' database need to be given to the user that runs the analyser.
Here is an example of how to do it with Ubuntu system:

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

Examples:

 * Derivative sensitivity analysis:

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

 * Derivative sensitivity analysis for time series:

      dist/build/banach/banach -QDt ts4.time1:time2:prov --db-create-tables tsschema.sql tsquery5.sql empty_attacker.att --epsilon 1.0 --beta 0.1

   where
   - column time1 of table ts0 contains the times when each row is added to table ts0
   - column time2 of table ts0 contains the times when each row is removed from table ts0
   - column prov of table ts0 contains the provenance of each row
   - comma-separated list of time columns in multiple tables can also be used, e.g. -QDt ts0.time1:time2:prov,ts1.time1:time2:prov
   - time2 and prov can be empty strings if row removals and/or provenances are not used, e.g. -QDt ts0.time1::prov,ts1.time1:time2

   The analysis processes times 1,2,3,...
   After processing each time point, it waits for a newline from standard input.
   The string `d` can be entered to enable debugging output for the current time point.
   The string `D` can be entered for even more debugging output.
   When processing a time point, the analyzer processes the rows added at that time and outputs the results about
   that time point and the combined results so far.

 * Guessing advantage analysis:

     dist/build/banach/banach -QDp --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --policy=demo_attacker_goal.sql --epsilon 0.3

   where
   - demo_attacker_goal.sql is the query representing the attacker's goal, i.e. what he is trying to guess with which precision
   - epsilon is the desired upper bound on guesing advantage

 * Combined sensitivity analysis (assumes that pleak-sql-analysis/localsensitivity-cabal has been built):
   Make sure that access is granted to a file that connects two analysers together:

     chmod a+x sqlsa-quiet

   The example itself:

     dist/build/banach/banach -QDc --db-create-tables demo_schema.sql demo_query.sql demo_constraints.att --epsilon 1.0 --beta 0.1 --distance-G=1.0

