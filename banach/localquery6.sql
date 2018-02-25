SELECT t5.d3,t5.d1,t5.d2,t6.d2,t6.d3
FROM
    (SELECT t1.c1 as d1,t1.c2 as d2,t2.c2 as d3
	FROM t1, t2 where t1.c1 = t2.c1)
    as t5,
    (SELECT t3.c1 as d1,t3.c2 as d2,t4.c2 as d3
	FROM t3, t4 where t3.c1 = t4.c1 and t3.c1 <= 10)
    as t6
WHERE t5.d3 = t6.d1;

