--SELECT sum(3 * t12.c2) FROM t11, t12 where t11.c1 = t12.c1;
SELECT sum(t11.c2 * t12.c2) FROM t11, t12 where t11.c1 = t12.c1;
