select sum(lineitem.l_extendedprice * (1 - lineitem.l_discount) )
from
    lineitem,
    part
where
part.p_partkey = lineitem.l_partkey
and lineitem.l_shipmode in ('AIR', 'AIR REG')
and lineitem.l_shipinstruct = 'DELIVER IN PERSON'
and part.p_size >= 1
and
((
part.p_brand = 'Brand#34'
and part.p_container in ('SM CASE', 'SM BOX', 'SM PACK', 'SM PKG')
and lineitem.l_quantity >= 35 and lineitem.l_quantity <= 35 + 10
and part.p_size <= 5
)
or
(
part.p_brand = 'Brand#22'
and part.p_container in ('MED BAG', 'MED BOX', 'MED PKG', 'MED PACK')
and lineitem.l_quantity >= 12 and lineitem.l_quantity <= 12 + 10
and part.p_size  <= 10
)
or
(
part.p_brand = 'Brand#14'
and part.p_container in ('LG CASE', 'LG BOX', 'LG PACK', 'LG PKG')
and lineitem.l_quantity >= 90 and lineitem.l_quantity <= 90 + 10
and part.p_size  <= 15
));
