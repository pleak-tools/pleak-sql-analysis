# SQL derivative sensitivity analysis tool for pleak.io

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


If PostgreSQL has not been installed yet, it needs to be done before running. The analyser has been tested with version 9.5.13.

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
The executable is created in the subdirectory dist/build/banach, thus to execute it:
    dist/build/banach/banach


Examples:

 * Derivative sensitivity analysis:

      dist/build/banach/banach -QD --db-create-tables demo_schema.sql demo_query.sql demo_attacker.att --epsilon 1.0 --beta 0.1

   where
    - demo_schema.sql contains the database schema
    - demo_query.sql contains the query
    - default_attacker.att (allowed to be an empty file) is the description of constraints on attributes
    The parameters epsilon and beta are optional.

The parameter --db-create-tables reads data from .db files and stores it to PostgreSQL database. Hence, if the data has already been uploaded once and it has not been updated, there is no need to create the tables again, and --db-create-tables can be removed.

 * Guessing advantage analysis:

     dist/build/banach/banach -QDp --db-create-tables demo_schema.sql demo_query.sql demo_attacker.att --policy=demo_policy.plc --epsilon 0.3 --beta 0.0

   where
   - demo_policy.plc contains the attributes that the attacker tries to guess, and the corresponding precision

 * Combined sensitivity analysis (assumes that pleak-sql-analysis/localsensitivity-cabal has been built):
   Make sure that access is granted to a file that connects two analysers together:

     chmod a+x sqlsa-quiet

   The example itself:

     dist/build/banach/banach -QDc --db-create-tables demo_schema.sql demo_query.sql demo_attacker.att --epsilon 1.0 --beta 0.1 --distance-G=1.0
