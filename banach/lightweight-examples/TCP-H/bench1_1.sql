select
    sum(lineitem.l_quantity)
from
    lineitem
where
    lineitem.l_shipdateF <= 6910 - 900
AND
    lineitem.l_returnflag = 'R'
and
    lineitem.l_linestatus = 'F'
;
