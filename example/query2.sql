SELECT DISTINCT t1.a1+1,t1.a2,t2.b1,t2.b2,t3.c1,t3.c2 FROM t1, t2, t3 where t2.b1 = t1.a1+2 and t3.c1 = t1.a1+3;
