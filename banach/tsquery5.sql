SELECT SUM(ta.c2*tb.c2+ts5.c2) FROM ts4 as ta, ts4 as tb, ts5 where ta.c1 = ts5.c1 and ta.c1 = tb.c1;
