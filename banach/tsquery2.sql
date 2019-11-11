SELECT SUM(ta.c2*tb.c2+ts1.c2) FROM ts0 as ta, ts0 as tb, ts1 where ta.c1 = ts1.c1 and ta.c1 = tb.c1;
