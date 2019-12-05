select
    sum(lineitem.l_extendedprice * (1 - lineitem.l_discount) - partsupp.ps_supplycost * lineitem.l_quantity)
from
    part,
    supplier,
    lineitem,
    partsupp,
    orders,
    nations
where
    supplier.s_suppkey = lineitem.l_suppkey
    and partsupp.ps_suppkey = lineitem.l_suppkey
    and partsupp.ps_partkey = lineitem.l_partkey
    and part.p_partkey = lineitem.l_partkey
    and orders.o_orderkey = lineitem.l_orderkey
    and supplier.s_nationkey = nations.n_nationkey
    and part.p_name like '%violet%'
    and nations.n_name = 'UNITED KINGDOM'
;
