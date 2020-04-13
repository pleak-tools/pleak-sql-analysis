INSERT INTO aggr_count SELECT COUNT(ship.ship_id) AS cnt FROM port AS port, parameters AS parameters, ship AS ship WHERE ((port.name = parameters.portname) AND (((POINT(ship.latitude,ship.longitude) <@> POINT(port.latitude,port.longitude)) / ship.max_speed) <= parameters.deadline));

INSERT INTO result SELECT port.port_id AS name, MAX(res.cnt) AS cnt FROM port AS port, aggr_count AS res GROUP BY port.port_id;

