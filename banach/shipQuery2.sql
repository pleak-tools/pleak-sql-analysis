SELECT MIN (suitable_port.time)
FROM
    (SELECT ship_port_distances.port_id AS port_id, ship_port_distances.ship_id AS ship_id, ship_port_distances.time AS time
	FROM
        (SELECT ship.ship_id AS ship_id, port.port_id AS port_id, ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed AS time, ship.length AS length 
	    FROM ship, port
        WHERE port.available)
        AS ship_port_distances,
        berth
    WHERE berth.port_id = ship_port_distances.port_id AND ship_port_distances.length <= berth.berthlength)
    AS suitable_port
;
