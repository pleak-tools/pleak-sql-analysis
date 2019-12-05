select
    sum(lineitem.l_extendedprice*(1-lineitem.l_discount))
from
    lineitem
where
    lineitem.l_shipdateF <= 6910 - 900
and
    lineitem.l_returnflag = 'R'
and
    lineitem.l_linestatus = 'F'
;
