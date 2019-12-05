select
sum(partsupp.ps_supplycost * partsupp.ps_availqty * 0.2)
from
partsupp,
supplier,
nations
where
partsupp.ps_suppkey = supplier.s_suppkey
and supplier.s_nationkey = nations.n_nationkey
and nations.n_name = 'JAPAN'
;
