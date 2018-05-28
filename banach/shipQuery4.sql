INSERT INTO mintime
SELECT min (((ship3.latitude - port3.latitude) ^ 2 + (ship3.longitude - port3.longitude) ^ 2) ^ 0.5 / ship3.max_speed)
FROM ship AS ship1, port AS port1, ship AS ship2, port AS port2, berth, ship AS ship3, port AS port3
WHERE port1.available AND
      port2.available AND
      port3.available AND
      berth.port_id = port2.port_id AND
      port3.port_id = port2.port_id AND
      ship3.ship_id = ship2.ship_id AND
      port3.port_id = port1.port_id AND
      ship3.ship_id = ship1.ship_id AND
      ship2.length <= berth.berthlength AND
      ((ship1.latitude - port1.latitude) ^ 2 + (ship1.longitude - port1.longitude) ^ 2) ^ 0.5 <= 1000
;
