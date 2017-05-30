CREATE TABLE ship (
  ship_id int4 PRIMARY KEY,
  name text NOT NULL,
  cargo int4,
  latitude int8,
  longitude int8,
  length int4,
  draft int4,
  maxspeed int4
);

CREATE TABLE port (
  port_id int4 PRIMARY KEY,
  name text NOT NULL,
  latitude int8,
  longitude int8,
  offloadcapacity int4,
  offloadtime int4,
  harbordepth int4,
  available bool
);

CREATE TABLE berth (
  port_id int4,
  berth_id int4,
  berthlength int4,
  PRIMARY KEY (port_id, berth_id)
);

CREATE TABLE reachable_ports (
  port_id int4 PRIMARY KEY,
  arrival int4
);

CREATE TABLE feasible_ports (
  port_id int4 PRIMARY KEY
);

CREATE TABLE available_slots (
  port_id int4,
  berth_id int4,
  slot_id int4,
  ship_id int4 REFERENCES ship NOT NULL,
  slotstart int4,
  slotend int4,
  PRIMARY KEY (port_id, berth_id, slot_id)
);

