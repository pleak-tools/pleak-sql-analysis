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

-- execute a list of queries (e.g. SELECT) that do not change the database
sendQueriesToDb :: ProgramOptions -> [String] -> IO ()
sendQueriesToDb args qs = withDb args $ \ conn -> do mapM_ (quickQuery' conn `flip` []) qs

-- execute a query that returns a single floating-point value
sendDoubleQueryToDb :: ProgramOptions -> String -> IO Double
sendDoubleQueryToDb args q = do
  [[res]] <- sendQueryToDb args q
  -- DB may return NULL of there are no sensitive rows and minimum is computed over row sensitivity
  -- TODO In general, need to verify if 0.0 is a valid substitute, if there will be more cases returning SqlNull.
  -- maybe, some special message "the query does not depend on sensitive data" would be more reasonable
  return (if res == SqlNull then 0.0 else fromSql res)

-- execute a query that returns a string and a single floating-point value
sendStringDoubleQueryToDb :: ProgramOptions -> String -> IO (String,Double)
sendStringDoubleQueryToDb args q = do
  [[res1,res2]] <- sendQueryToDb args q
  -- DB may return NULL of there are no sensitive rows and minimum is computed over row sensitivity
  -- TODO In general, need to verify if 0.0 is a valid substitute, if there will be more cases returning SqlNull.
  -- maybe, some special message "the query does not depend on sensitive data" would be more reasonable
  return (if res1 == SqlNull then "" else fromSql res1, if res2 == SqlNull then 0.0 else fromSql res2)

-- execute a query that returns a list of single string and a floating-point value pairs
sendStringsDoublesQueryToDb :: ProgramOptions -> String -> IO [(String,Double)]
sendStringsDoublesQueryToDb args q = do
  putStrLn $ "----------------"
  putStrLn $ show q
  results <- sendQueryToDb args q
  -- DB may return NULL of there are no sensitive rows and minimum is computed over row sensitivity
  -- TODO In general, need to verify if 0.0 is a valid substitute, if there will be more cases returning SqlNull.
  -- maybe, some special message "the query does not depend on sensitive data" would be more reasonable
  return $ map (\ [res1,res2] -> (if res1 == SqlNull then "" else fromSql res1, if res2 == SqlNull then 0.0 else fromSql res2)) results
