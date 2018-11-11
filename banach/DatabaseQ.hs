module DatabaseQ where

import ProgramOptions
import Database.HDBC
import Database.HDBC.PostgreSQL

withDb :: ProgramOptions -> (Connection -> IO a) -> IO a
withDb args = withPostgreSQL' (dbConnString args)

-- execute a list of queries (e.g. CREATE/DROP TABLE) that change the database and commit the changes
sendQueriesToDbAndCommit :: ProgramOptions -> [String] -> IO ()
sendQueriesToDbAndCommit args qs = withDb args $ \ conn -> do mapM_ (quickQuery' conn `flip` []) qs
                                                              commit conn

-- execute a query (e.g. SELECT) that does not change the database
sendQueryToDb :: ProgramOptions -> String -> IO [[SqlValue]]
sendQueryToDb args q = withDb args $ \ conn -> quickQuery' conn q []

-- execute a query that returns a single floating-point value
sendDoubleQueryToDb :: ProgramOptions -> String -> IO Double
sendDoubleQueryToDb args q = do
  [[res]] <- sendQueryToDb args q
  -- DB may return NULL of there are no sensitive rows and minimum is computed over row sensitivity
  -- TODO In general, need to verify if 0.0 is a valid substitute, if there will be more cases returning SqlNull.
  -- maybe, some special message "the query does not depend on sensitive data" would be more reasonable
  return (if res == SqlNull then 0.0 else fromSql res)
