mintime =
SELECT min (((ships.latitude - ports.latitude) ^ 2 + (ships.longitude - ports.longitude) ^ 2) ^ 0.5 / ships.maxspeed)
FROM ships, ports, berth
WHERE ports.available AND
      berth.port_id = ports.port_id AND
      ships.length <= berth.berthlength AND
      ((ships.latitude - ports.latitude) ^ 2 + (ships.longitude - ports.longitude) ^ 2) ^ 0.5 <= 1000
