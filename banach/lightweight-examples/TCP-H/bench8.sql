		select
			sum(lineitem.l_extendedprice * (1 - lineitem.l_discount))
		from
			part,
			supplier,
			lineitem,
			orders,
			customer,
			nations AS n1,
			nations AS n2,
			region
		where
			part.p_partkey = lineitem.l_partkey
			and supplier.s_suppkey = lineitem.l_suppkey
			and lineitem.l_orderkey = orders.o_orderkey
			and orders.o_custkey = customer.c_custkey
			and customer.c_nationkey = n1.n_nationkey
			and n1.n_regionkey = region.r_regionkey
			and region.r_name = 'ASIA'
			and supplier.s_nationkey = n2.n_nationkey
                        and orders.o_orderdateF >= 5478
                        and orders.o_orderdateF <= 6210
			and part.p_type = 'MEDIUM BRUSHED COPPER'
                        and n2.n_name = 'JAPAN'
;
