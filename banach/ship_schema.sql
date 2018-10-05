CREATE TABLE parameters2 (  param_id INT8 PRIMARY KEY, deadline INT8, shipname TEXT);
create table ship (  ship_id INT8 primary key,  name TEXT,  cargo INT8,  latitude INT8,  longitude INT8,  length FLOAT8,  draft INT8,  max_speed INT8);
create table port (  port_id INT8 primary key,  name TEXT,  latitude INT8,  longitude INT8,  offloadcapacity INT8,   offloadtime INT8,  harbordepth INT8,  available Bool);
create table berth (  port_id INT8,  berth_id INT8,  berthlength FLOAT8);
CREATE TABLE slot (  port_id INT8, berth_id INT8, slot_id INT8, ship_id INT8, slotstart INT8, slotend INT8);

