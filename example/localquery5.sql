SELECT DISTINCT COUNT(*),ta.c1,ta.c2,tb.c2,tc.c1 FROM t2 as ta, t2 as tb, t1 as tc where ta.c1 = tb.c1 AND ta.c2 <= 2 AND tb.c2 = tc.c2;
