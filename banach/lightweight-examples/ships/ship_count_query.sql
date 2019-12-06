INSERT INTO reaching_times SELECT
    port.port_id AS port_id,
    ship.ship_id AS ship_id,
    (((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed) AS arrival
FROM port, ship, ship_parameters
WHERE
    port.name = ship_parameters.portname
;

INSERT INTO feasible_ships SELECT
    port.port_id AS port_id,
    ship.ship_id AS ship_id
FROM port, ship, ship_parameters
WHERE
    port.harbordepth >= ship.draft
    AND port.offloadcapacity >= ship.cargo
    AND port.name = ship_parameters.portname
;

INSERT INTO ship_arrival_to_port SELECT
    count(*)
FROM
    reaching_times AS reachable,
    feasible_ships AS feasible,
    port, slot, berth, ship, ship_parameters
WHERE
    ship.ship_id = feasible.ship_id
    AND reachable.ship_id = feasible.ship_id
    AND reachable.port_id = feasible.port_id
    AND reachable.port_id = port.port_id
    AND port.port_id = berth.port_id
    AND slot.port_id = berth.port_id
    AND slot.berth_id = berth.berth_id
    AND berth.berthlength >= ship.length
    AND slot.slotstart <= ship_parameters.deadline
    AND slot.slotstart + port.offloadtime <= slot.slotend
    AND reachable.arrival <= 20
;
