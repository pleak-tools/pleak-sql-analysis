reachable_ports =
SELECT
    port.port_id AS port_id,
    ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed AS arrival
FROM port, ship, parameters
WHERE
    ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed <= parameters.deadline
    AND ship.name = parameters.shipname

feasible_ports =
SELECT
    port.port_id AS port_id
FROM reachable_ports, port, ship, parameters
WHERE
    reachable_ports.port_id = port.port_id
    AND port.available = 1.0
    AND port.harbordepth >= ship.draft
    AND port.offloadcapacity >= ship.cargo
    AND ship.name = parameters.shipname

ship_arrival_to_port =
SELECT min(rport.arrival)
FROM
    reachable_ports AS rport,
    feasible_ports AS fport,
    port, slot, berth, ship, parameters
WHERE
    port.port_id = fport.port_id
    AND port.port_id = rport.port_id
    AND port.port_id = berth.port_id
    AND slot.port_id = berth.port_id
    AND slot.berth_id = berth.berth_id
    AND ship.name = parameters.shipname
    AND berth.berthlength >= ship.length
    AND slot.slotstart <= parameters.deadline
    AND slot.slotstart + port.offloadtime <= slot.slotend
