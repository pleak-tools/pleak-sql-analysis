module Catalog where

import Database.HsSqlPpp.Catalog
import Database.HsSqlPpp.Dialect

-- Currently just use postgres dialect
-- TODO: use a simpler custom catalog
catalog :: Catalog
catalog = case updateCatalog [] (diDefaultCatalog postgresDialect) of
  Left err -> error $ show err
  Right cat -> cat
