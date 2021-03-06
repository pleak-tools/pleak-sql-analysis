SELECT min (((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed)
FROM ship, port, berth
WHERE port.available AND
      berth.port_id = port.port_id AND
      ship.length <= berth.berthlength AND
      ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 <= 1000
;
