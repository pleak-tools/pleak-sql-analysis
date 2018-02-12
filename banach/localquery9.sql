SELECT COUNT(*) FROM t1, t2, t2copy where t1.c1 = t2.c1 AND t2.c1 = t2copy.c1
