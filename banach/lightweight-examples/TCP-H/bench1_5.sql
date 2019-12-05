select
    count(*)
from
    lineitem
where
    lineitem.l_shipdateF <= 6910 - 900
and
    lineitem.l_returnflag = 'R'
and
    lineitem.l_linestatus = 'F'
;
