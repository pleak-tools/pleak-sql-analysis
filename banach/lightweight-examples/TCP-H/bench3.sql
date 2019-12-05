select sum(lineitem.l_extendedprice * (1 - lineitem.l_discount))
from
    customer,
    orders,
    lineitem
where
    customer.c_mktsegment = 'BUILDING'
and customer.c_custkey = orders.o_custkey
and lineitem.l_orderkey = orders.o_orderkey
and orders.o_orderdateF < 5700
and lineitem.l_shipdateF > 5700
and lineitem.l_orderkey = '162'
and orders.o_shippriority = '0'
;
