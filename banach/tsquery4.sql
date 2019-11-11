SELECT SUM(ta.c2*tb.c2+ts3.c2) FROM ts2 as ta, ts2 as tb, ts3 where ta.c1 = ts3.c1 and ta.c1 = tb.c1;
