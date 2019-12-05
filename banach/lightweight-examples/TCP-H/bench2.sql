select
min(partsupp.ps_supplycost)
from
partsupp, supplier,
nations, region, part
where
part.p_partkey = partsupp.ps_partkey
and supplier.s_suppkey = partsupp.ps_suppkey
and supplier.s_nationkey = nations.n_nationkey
and nations.n_regionkey = region.r_regionkey
and region.r_name = 'ASIA'
;
