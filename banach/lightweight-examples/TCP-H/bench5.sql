select sum(lineitem.l_extendedprice * (1 - lineitem.l_discount))
from
    customer,
    orders,
    lineitem,
    supplier,
    nations,
    region
where
    customer.c_custkey = orders.o_custkey
    and lineitem.l_orderkey = orders.o_orderkey
    and lineitem.l_suppkey = supplier.s_suppkey
    and customer.c_nationkey = supplier.s_nationkey
    and supplier.s_nationkey = nations.n_nationkey
    and nations.n_regionkey = region.r_regionkey
    and region.r_name = 'ASIA'
    and orders.o_orderdateF >= 6400
    and orders.o_orderdateF < 6400 + 360
    and nations.n_name = 'JAPAN'
;
