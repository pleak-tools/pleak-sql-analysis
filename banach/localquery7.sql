SELECT t2.c2,t1.c1,t1.c2,t3.c2,t4.c2
FROM t1,t2,t3,t4
WHERE t2.c2 = t3.c1 and t1.c1 = t2.c1 and t3.c1 = t4.c1 and t3.c1 <= 10;
