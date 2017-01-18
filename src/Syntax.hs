
--
-- As first approximation we want to support:
--  SELECT, FROM, WHERE and GROUP BY
-- and aggregation with min, max and possibly count. No subqueries at first.
--
-- Need to track location information and possibly remain compatible with
-- hssqlppp abstract syntax.
--
