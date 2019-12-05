select
    count(*)
from
    orders,
    lineitem
where
    orders.o_orderkey = lineitem.l_orderkey
    and (orders.o_orderpriority <> '1-URGENT' or orders.o_orderpriority <> '2-HIGH')
    and lineitem.l_shipmode in ('TRUCK', 'SHIP')
    and lineitem.l_commitdateF < lineitem.l_receiptdateF
    and lineitem.l_shipdateF < lineitem.l_commitdateF
    and lineitem.l_receiptdateF >= 5500
    and lineitem.l_receiptdateF < 5500 + 360
;
