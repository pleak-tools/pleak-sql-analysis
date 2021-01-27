CREATE TABLE parameters ( param_id INT8 PRIMARY KEY, deadline INT8, portname TEXT);
create table ship ( 
  ship_id INT8 primary key, 
  name TEXT, 
  cargo INT8, 
  latitude INT8, 
  longitude INT8,
  max_speed INT8);
create table port ( 
  port_id INT8 primary key, 
  name TEXT, 
  latitude INT8, 
  longitude INT8, 
  offloadcapacity INT8, 
  offloadtime INT8,
  available Bool);
create table berth (  port_id INT8,  berth_id INT8);
CREATE TABLE slot (
  slot_id INT8 primary key, 
  port_id INT8, 
  berth_id INT8, 
  slotstart INT8, 
  slotend INT8);

CREATE TABLE public_key ( param_id INT8 PRIMARY KEY, keyvalue TEXT);
CREATE TABLE private_key ( param_id INT8 PRIMARY KEY, keyvalue TEXT);

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
 name TEXT, cnt INT8);

create table aggr_count (
 name TEXT, cnt INT8);

create table capacities (
 portname TEXT,
 slots_number INT8);

create table ship_count (
 name TEXT,
 num_of_ships INT8);
