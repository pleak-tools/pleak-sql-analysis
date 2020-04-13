INSERT INTO port_enc SELECT port.available AS available, port.latitude AS latitude, port.longitude AS longitude, port.name AS name, port.offloadcapacity AS offloadcapacity, port.offloadtime AS offloadtime, port.port_id AS port_id FROM port AS port;

INSERT INTO count_ships SELECT COUNT(ship.ship_id) AS cnt FROM port_enc AS port_enc, parameters AS parameters, ship AS ship WHERE ((port_enc.name = parameters.portname) AND ((((((ship.latitude + (-(port_enc.latitude))) ^ 2) + ((ship.longitude + (-(port_enc.longitude))) ^ 2)) ^ 0.5) / ship.max_speed) <= parameters.deadline));

INSERT INTO aggr_count_enc SELECT p.name AS name, res.cnt AS cnt FROM port_enc AS p, count_ships AS res;

INSERT INTO aggr_count SELECT ac2.cnt AS cnt, ac2.name AS name FROM aggr_count_enc AS ac2;

INSERT INTO slots_count SELECT COUNT(slot.slot_id) AS slots_number FROM port AS port, parameters AS parameters, berth AS berth, slot AS slot WHERE ((port.name = parameters.portname) AND (port.port_id = berth.port_id) AND (slot.port_id = berth.port_id) AND (slot.berth_id = berth.berth_id) AND (slot.slotstart <= parameters.deadline) AND ((slot.slotstart + port.offloadtime) <= slot.slotend));

INSERT INTO capacities SELECT p.name AS portname, res.slots_number AS slots_number FROM port AS p, slots_count AS res;

INSERT INTO ship_count SELECT ac.name AS name, (LEAST(ac.cnt,cp.slots_number)) AS num_of_ships FROM aggr_count AS ac, capacities AS cp, parameters AS parameters WHERE ((ac.name = cp.portname) AND (ac.name = parameters.portname));

INSERT INTO result SELECT port.name AS name, MAX(sc.num_of_ships) AS num_of_ships FROM ship_count AS sc, port AS port WHERE (sc.name = port.name) GROUP BY port.name;

