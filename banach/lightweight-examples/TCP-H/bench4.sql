select count(*)
from
    orders,
    lineitem
where
    orders.o_orderdateF >= 5400
    and orders.o_orderdateF < 5400 + 90
    and lineitem.l_orderkey = orders.o_orderkey
    and lineitem.l_commitdateF < lineitem.l_receiptdateF
    and orders.o_orderpriority = '1-URGENT'
;
