SELECT DISTINCT t2.num FROM t1, t2 WHERE t2.id >= 6*t1.id AND t2.id < 6*(t1.id+1)
