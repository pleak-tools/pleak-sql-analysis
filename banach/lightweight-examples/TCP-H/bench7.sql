select
    sum(lineitem.l_extendedprice * (1 - lineitem.l_discount))
from
    supplier,
    lineitem,
    orders,
    customer,
    nations as n1,
    nations as n2
where
    supplier.s_suppkey = lineitem.l_suppkey
    and orders.o_orderkey = lineitem.l_orderkey
    and customer.c_custkey = orders.o_custkey
    and supplier.s_nationkey = n1.n_nationkey
    and customer.c_nationkey = n2.n_nationkey
    and (
        (n1.n_name = 'JAPAN' and n2.n_name = 'INDONESIA')
        or (n1.n_name = 'INDONESIA' and n2.n_name = 'JAPAN')
    )
    and lineitem.l_shipdateF >= 5478
    and lineitem.l_shipdateF <= 6210
;
