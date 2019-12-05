select count(partsupp.ps_suppkey)
from
    partsupp,
    part,
    supplier
where
part.p_partkey = partsupp.ps_partkey
and partsupp.ps_suppkey = supplier.s_suppkey
and part.p_brand <> 'Brand#34'
and not (part.p_type like '%COPPER%')
and part.p_size in (5, 10, 15, 20, 25, 30, 35, 40)
and not (supplier.s_comment like '%Customer%Complaints%')
;
