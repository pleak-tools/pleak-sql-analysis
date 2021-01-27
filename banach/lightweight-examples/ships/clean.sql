INSERT INTO compute_reachable_ports SELECT port.port_id AS port_id, (CEIL(((POINT(ship.longitude,ship.latitude) <@> POINT(port.longitude,port.latitude)) / ship.maxspeed))) AS arrival FROM ship AS ship, port AS port, parameters AS parameters WHERE (((CEIL(((POINT(ship.longitude,ship.latitude) <@> POINT(port.longitude,port.latitude)) / ship.maxspeed))) <= parameters.deadline) AND (ship.name = parameters.shipname) AND (port.port_id = port.port_id));

INSERT INTO reachable_ports SELECT rports.arrival AS arrival, rports.port_id AS port_id FROM parameters AS p, compute_reachable_ports AS rports;

INSERT INTO compute_feasible_ports SELECT port.port_id AS undefined FROM reachable_ports AS reachable_ports, port AS port, ship AS ship, parameters AS parameters WHERE ((reachable_ports.port_id = port.port_id) AND port.available AND (port.harbordepth >= ship.draft) AND (port.offloadcapacity >= ship.cargo) AND (ship.name = parameters.shipname));

INSERT INTO feasible_ports SELECT  FROM parameters AS p, compute_feasible_ports AS compute_feasible_ports;

INSERT INTO compute_available_slots SELECT row_number() AS gap_id FROM slot AS s ORDER BY slotstart, gap;

INSERT INTO available_slots SELECT  FROM compute_available_slots AS compute_available_slots;

INSERT INTO assign_slots SELECT p.port_id AS port_id, (LEAST(rp.arrival,aslot.slotstart)) AS offloadstart FROM port AS p, feasible_ports AS feasible_ports, reachable_ports AS rp, berth AS b, available_slots AS available_slots, ship AS s, parameters AS parameters WHERE ((p.port_id = fp.port_id) AND (p.port_id = rp.port_id) AND (p.port_id = b.port_id) AND (aslot.port_id = b.port_id) AND (aslot.berth_id = b.berth_id) AND (s.name = parameters.shipname) AND (b.berthlength >= s.length) AND (rp.arrival <= parameters.deadline) AND (aslot.slotstart <= parameters.deadline) AND ((rp.arrival + p.offloadtime) <= aslot.slotend) AND ((aslot.slotstart + p.offloadtime) <= aslot.slotend));

INSERT INTO slot_assignments SELECT sa.offloadstart AS offloadstart, sa.port_id AS port_id FROM parameters AS p, assign_slots AS sa;

