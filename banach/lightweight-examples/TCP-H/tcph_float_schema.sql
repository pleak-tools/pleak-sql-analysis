CREATE TABLE part (
    p_partkey int8,
    p_name text,
    p_mfgr text,
    p_brand text,
    p_type text,
    p_size int8,
    p_container text,
    p_retailprice float8,
    p_comment text
);

CREATE TABLE supplier (
    s_suppkey int8,
    s_name text,
    s_address text,
    s_nationkey int8,
    s_phone text,
    s_acctbal float8,
    s_comment text
);

CREATE TABLE partsupp (
    ps_partkey int8,
    ps_suppkey int8,
    ps_availqty int8,
    ps_supplycost float8,
    ps_comment text
);

CREATE TABLE customer (
    c_custkey int8,
    c_name text,
    c_address text,
    c_nationkey int8,
    c_phone text,
    c_acctbal float8,
    c_mktsegment text,
    c_comment text
);

CREATE TABLE orders (
    o_orderkey int8,
    o_custkey int8,
    o_orderstatus text,
    o_totalprice float8,
    o_orderdateF float8,
    o_orderpriority text,
    o_clerk text,
    o_shippriority int8, 
    o_comment text
);

CREATE TABLE lineitem (
    l_orderkey int8,
    l_partkey int8,
    l_suppkey int8,
    l_linenumber int8,
    l_quantity int8,
    l_extendedprice float8,
    l_discount float8,
    l_tax float8,
    l_returnflag text,
    l_linestatus text,
    l_shipdateF float8,
    l_commitdateF float8,
    l_receiptdateF float8,
    l_shipinstruct text,
    l_shipmode text,
    l_comment text
);

CREATE TABLE nations (
    n_nationkey int8,
    n_name text,
    n_regionkey int8,
    n_comment text
);

CREATE TABLE region (
   r_regionkey int8,
   r_name text,
   r_comment text
);

