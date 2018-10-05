INSERT INTO reachable_ports SELECT
    port.port_id AS port_id,
    ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed AS arrival
FROM port, ship, parameters2
WHERE
    ship.name = parameters2.shipname
;

INSERT INTO feasible_ports SELECT
    port.port_id AS port_id
FROM reachable_ports, port, ship, parameters2
WHERE
    reachable_ports.port_id = port.port_id
    AND port.available
    AND port.harbordepth >= ship.draft
    AND port.offloadcapacity >= ship.cargo
    AND ship.name = parameters2.shipname
;

INSERT INTO ship_arrival_to_port SELECT
    min(rport.arrival)
FROM
    reachable_ports AS rport,
    feasible_ports AS fport,
    port, slot, berth, ship, parameters2
WHERE
    port.port_id = fport.port_id
    and port.port_id = rport.port_id
    AND port.port_id = berth.port_id
    AND slot.port_id = berth.port_id
    AND slot.berth_id = berth.berth_id
    AND ship.name = parameters2.shipname
    AND berth.berthlength >= ship.length
    AND slot.slotstart <= parameters2.deadline
    AND slot.slotstart + port.offloadtime <= slot.slotend
;
