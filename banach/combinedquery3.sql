SELECT SUM(t11.c2*t12.c2+t3.c2) FROM t11, t12, t12 as t3 where t11.c1 = t12.c1 and t11.c2 <= t12.c2 and t12.c1 = t3.c1;
