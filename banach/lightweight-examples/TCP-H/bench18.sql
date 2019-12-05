insert into
    temporary
select
    customer.c_name AS c_name,
    customer.c_custkey AS c_custkey,
    orders.o_orderkey AS o_orderkey,
    sum(lineitem.l_quantity) AS sumq
from
    customer,
    orders,
    lineitem
where
    customer.c_custkey = orders.o_custkey
    and orders.o_orderkey = lineitem.l_orderkey
group by
    customer.c_name,
    customer.c_custkey,
    orders.o_orderkey
;

select
    min(temp.sumq)
from
    temporary as temp
where
    temp.sumq > 100
;
