SELECT SUM(t11.c2 * t12.c2^2) FROM t11, t12 where t11.c1 = t12.c1 and t11.c2 >= 3;
