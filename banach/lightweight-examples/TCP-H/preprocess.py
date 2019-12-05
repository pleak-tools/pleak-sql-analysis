from math import *
from random import *
from dateutil.parser import parse
import datetime

#######################################################
# This code converts datatypes to integers
# and creates .nrm and .db files from TPC-H tables
#######################################################
d = "|"

fin      = open('orders0.01.tbl', 'r')
fout_db  = open('orders.db',  'w')
fout_nrm = open('orders.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: o_totalprice o_orderdateF;\n")
fout_nrm.write("\n")
fout_nrm.write("e = scaleNorm 0.01 o_totalprice;\n")
fout_nrm.write("s = scaleNorm 1.0 o_orderdateF;\n")
fout_nrm.write("z = lp 1.0 e s;\n")
fout_nrm.write("return lp 1.0 z;\n")

fout_db.write("o_orderkey" + d + "o_custkey" + d + "o_orderstatus" + d + "o_totalprice" + d + "o_orderdateF" + d)
fout_db.write("o_orderpriority" + d + "o_clerk" + d + "o_shippriority" + d + "o_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    elems[4] = (parse(elems[4]).date() - datetime.date(1980, 1, 1)).days
    newline_db  = ""
    elems[2] = '\'' + elems[2] + '\''
    elems[5] = '\'' + elems[5] + '\''
    elems[6] = '\'' + elems[6] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('lineitem0.01.tbl', 'r')
fout_db  = open('lineitem.db',  'w')
fout_nrm = open('lineitem.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: l_quantity l_extendedprice l_discount l_shipdateF l_commitdateF l_receiptdateF;\n")
fout_nrm.write("\n")
fout_nrm.write("q = scaleNorm 1.0 l_quantity;\n")
fout_nrm.write("e = scaleNorm 0.0001 l_extendedprice;\n")
fout_nrm.write("d = scaleNorm 50.0 l_discount;\n")
fout_nrm.write("s = linf l_shipdateF l_commitdateF l_receiptdateF;\n")
fout_nrm.write("t = scaleNorm 1.0 s;\n")
fout_nrm.write("u = lp 1.0 q e d t;\n")
fout_nrm.write("return lp 1.0 u;\n")

fout_db.write("l_orderkey" + d + "l_partkey" + d + "l_suppkey" + d + "l_linenumber" + d + "l_quantity" + d)
fout_db.write("l_extendedprice" + d + "l_discount" + d + "l_tax" + d + "l_returnflag" + d + "l_linestatus" + d)
fout_db.write("l_shipdateF" + d + "l_commitdateF" + d + "l_receiptdateF" + d + "l_shipinstruct" + d + "l_shipmode" + d + "l_comment\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    elems[10] = (parse(elems[10]).date() - datetime.date(1980, 1, 1)).days
    elems[11] = (parse(elems[11]).date() - datetime.date(1980, 1, 1)).days
    elems[12] = (parse(elems[12]).date() - datetime.date(1980, 1, 1)).days
    newline_db  = ""
    elems[8] = '\'' + elems[8] + '\''
    elems[9] = '\'' + elems[9] + '\''
    elems[13] = '\'' + elems[13] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('part0.01.tbl', 'r')
fout_db  = open('part.db',  'w')
fout_nrm = open('part.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: p_retailprice p_size;\n")
fout_nrm.write("\n")
fout_nrm.write("e = scaleNorm 0.01 p_retailprice;\n")
fout_nrm.write("s = scaleNorm 1.0 p_size;\n")
fout_nrm.write("z = lp 1.0 e s;\n")
fout_nrm.write("return lp 1.0 z;\n")

fout_db.write("p_partkey" + d + "p_name" + d + "p_mfgr" + d + "p_brand" + d + "p_type" + d)
fout_db.write("p_size" + d + "p_container" + d + "p_retailprice" + d + "p_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[1] = '\'' + elems[1] + '\''
    elems[2] = '\'' + elems[2] + '\''
    elems[3] = '\'' + elems[3] + '\''
    elems[4] = '\'' + elems[4] + '\''
    elems[6] = '\'' + elems[6] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('partsupp0.01.tbl', 'r')
fout_db  = open('partsupp.db', 'w')
fout_nrm = open('partsupp.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: ps_availqty ps_supplycost;\n")
fout_nrm.write("\n")
fout_nrm.write("e = scaleNorm 0.01 ps_supplycost;\n")
fout_nrm.write("s = scaleNorm 1.0 ps_availqty;\n")
fout_nrm.write("z = lp 1.0 e s;\n")
fout_nrm.write("return lp 1.0 z;\n")

fout_db.write("ps_partkey" + d + "ps_suppkey" + d + "ps_availqty" + d + "ps_supplycost" + d + "ps_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('supplier0.01.tbl', 'r')
fout_db  = open('supplier.db', 'w')
fout_nrm = open('supplier.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: s_acctbal;\n")
fout_nrm.write("\n")
fout_nrm.write("z = scaleNorm 0.01 s_acctbal;\n")
fout_nrm.write("return lp 1.0 z;\n")

fout_db.write("s_suppkey" + d + "s_name" + d + "s_address" + d + "s_nationkey" + d + "s_phone" + d + "s_acctbal" + d + "s_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[1] = '\'' + elems[1] + '\''
    elems[2] = '\'' + elems[2] + '\''
    elems[4] = '\'' + elems[4] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('customer0.01.tbl', 'r')
fout_db  = open('customer.db', 'w')
fout_nrm = open('customer.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: c_acctbal;\n")
fout_nrm.write("\n")
fout_nrm.write("z = scaleNorm 0.01 c_acctbal;\n")
fout_nrm.write("return lp 1.0 z;\n")

fout_db.write("c_custkey" + d + "c_name" + d + "c_address" + d + "c_nationkey" + d + "c_phone" + d + "c_acctbal" + d + "c_mktsegment" + d + "c_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[1] = '\'' + elems[1] + '\''
    elems[2] = '\'' + elems[2] + '\''
    elems[4] = '\'' + elems[4] + '\''
    elems[6] = '\'' + elems[6] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('nation.tbl',  'r')
fout_db  = open('nations.db',  'w')
fout_nrm = open('nations.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: none;\n")

fout_db.write("n_nationkey" + d + "n_name" + d + "n_regionkey" + d + "n_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[1] = '\'' + elems[1] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close

#-----------------------------------

fin      = open('region.tbl', 'r')
fout_db  = open('region.db',  'w')
fout_nrm = open('region.nrm', 'w')

fout_nrm.write("rows: all;\n")
fout_nrm.write("cols: none;\n")

fout_db.write("r_regionkey" + d + "r_name" + d + "r_comment" + d + "\n")
for line in fin:
    elems = (line.strip()).split("|")[:-1]
    newline_db  = ""
    elems[1] = '\'' + elems[1] + '\''
    elems[-1] = '\'' + elems[-1] + '\''
    for elem in elems:
        newline_db  = newline_db + str(elem) + d
    fout_db.write(newline_db + "\n")

fin.close
fout_db.close
fout_nrm.close
