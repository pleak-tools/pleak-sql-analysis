CREATE TABLE ship_parameters (  param_id INT8 PRIMARY KEY, deadline INT8, shipname TEXT, portname TEXT, port_id INT8);
CREATE TABLE parameters (  param_id INT8 PRIMARY KEY, deadline INT8, shipname TEXT, portname TEXT, port_id INT8);
create table ship (  ship_id INT8 primary key,  name TEXT,  cargo INT8,  latitude BIGINT,  longitude INT8,  length INT8,  draft INT8,  max_speed INT8);
create table port (  port_id BIGINT primary key,  name TEXT,  latitude BIGINT,  longitude BIGINT,  offloadcapacity BIGINT,   offloadtime INT8,  harbordepth INT8,  available Bool);
create table berth (  port_id INT8,  berth_id INT8,  berthlength INT8);
CREATE TABLE slot (  port_id INT8, berth_id INT8, slot_id INT8, ship_id INT8, slotstart INT8, slotend INT8);

create table reaching_times (  port_id INT8,  ship_id INT8, arrival INT8);
