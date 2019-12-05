select
    sum(lineitem.l_extendedprice * (1 - lineitem.l_discount))
from
    customer,
    orders,
    lineitem,
    nations
where
    customer.c_custkey = orders.o_custkey
    and lineitem.l_orderkey = orders.o_orderkey
    and orders.o_orderdateF >= 5500
    and orders.o_orderdateF <  5500 + 90
    and lineitem.l_returnflag = 'R'
    and customer.c_nationkey = nations.n_nationkey
    and customer.c_custkey = '64'
    and nations.n_name = 'CANADA'
;
