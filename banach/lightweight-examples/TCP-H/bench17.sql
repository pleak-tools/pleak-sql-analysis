select
    sum(lineitem.l_extendedprice * 0.142857)
from
    lineitem,
    part
where
    part.p_partkey = lineitem.l_partkey
    and part.p_brand = 'Brand#34'
    and part.p_container = 'JUMBO PKG'
    and lineitem.l_quantity < 0.2 * 32
;
