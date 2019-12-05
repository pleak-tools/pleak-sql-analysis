select
        sum(lineitem.l_extendedprice * lineitem.l_discount)
from
        lineitem
where
        lineitem.l_shipdateF >= 5115
        and lineitem.l_shipdateF < 5115 + 360
        and lineitem.l_discount between 0.09 - 0.01 and 0.09 + 0.01
        and lineitem.l_quantity < 24
;
