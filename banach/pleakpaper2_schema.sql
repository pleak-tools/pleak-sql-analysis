create table port 
( 
 port_id INT8 primary key, 
 name TEXT, 
 latitude INT8, 
 longitude INT8, 
 offloadcapacity INT8, 
 offloadtime INT8, 
 harbordepth INT8, 
 available Bool);

create table ship ( 
 ship_id INT8 primary key, 
 name TEXT, 
 cargo INT8, 
 latitude INT8, 
 longitude INT8, 
 length INT8, 
 draft INT8, 
 max_speed INT8);

CREATE TABLE ship_parameters 
( 
 param_id INT8 PRIMARY KEY, 
 deadline INT8, 
 portname TEXT);

create table berth (berth_id INT8 primary key, port_id INT8, berthlength INT8);

CREATE TABLE slot (slot_id INT8 primary key, port_id INT8, berth_id INT8, slotstart INT8, slotend INT8);

create table port_enc (
 port_id INT8 primary key, 
 name TEXT, 
 latitude INT8, 
 longitude INT8, 
 offloadcapacity INT8, 
 offloadtime INT8, 
 harbordepth INT8, 
 available Bool);

create table aggr_count_enc (
 pname TEXT, cnt INT8);

create table aggr_count (
 pname TEXT, cnt INT8);

create table capacities (
 slots_number INT8);
