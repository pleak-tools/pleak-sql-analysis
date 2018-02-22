SELECT MIN suitable_ports.time
FROM
    (SELECT ship_port_distances.port_id AS port_id, ship_port_distances.ship_id AS ship_id, ship_port_distances.time AS time
	FROM
        (SELECT ships.ship_id AS ship_id, ports.port_id AS port_id, sqrt(|(ships.latitude - ports.latitude)| ^ 2 + |(ships.longitude - ports.longitude)| ^ 2) / ships.maxspeed AS time, ships.length AS length 
	    FROM ships, ports
        WHERE ports.available == 1)
        AS ship_port_distances,
        berth
    WHERE berth.port_id - ship_port_distances.port_id == 0 AND ship_port_distances.length <= berth.berthlength)
    AS suitable_ports,
    feasible_ports
WHERE suitable_ports.port_id - feasible_ports.port_id == 0