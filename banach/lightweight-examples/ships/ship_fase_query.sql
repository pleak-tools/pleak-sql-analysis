INSERT INTO reachable_ports SELECT
    port.port_id AS port_id,
    ship.ship_id AS ship_id,
    (point(ship.latitude,ship.longitude) <@> point(port.latitude,port.longitude)) / ship.max_speed AS arrival
FROM port, ship
;

INSERT INTO feasible_ports SELECT
    port.port_id AS port_id,
    ship.ship_id AS ship_id
FROM port, ship, ship_parameters, slot
WHERE
    port.port_id = ship_parameters.port_id
    AND port.available
    AND port.harbordepth >= ship.draft
    AND port.offloadcapacity >= ship.cargo
    AND slot.port_id = port.port_id
    AND slot.slotstart <= ship_parameters.deadline
    AND slot.slotstart + port.offloadtime <= slot.slotend
;

SELECT
    MIN(rport.arrival) AS mintime
FROM
    reachable_ports AS rport,
    feasible_ports AS fport
WHERE
    rport.port_id = fport.port_id 
    AND rport.ship_id = fport.ship_id  
;
