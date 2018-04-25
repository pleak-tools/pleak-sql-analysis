mintime =
SELECT min (((ships3.latitude - ports3.latitude) ^ 2 + (ships3.longitude - ports3.longitude) ^ 2) ^ 0.5 / ships3.maxspeed)
FROM ships AS ships1, ports AS ports1, ships AS ships2, ports AS ports2, berth, ships AS ships3, ports AS ports3
WHERE ports1.available AND
      ports2.available AND
      ports3.available AND
      berth.port_id = ports2.port_id AND
      ports3.port_id = ports2.port_id AND
      ships3.ship_id = ships2.ship_id AND
      ports3.port_id = ports1.port_id AND
      ships3.ship_id = ships1.ship_id AND
      ships2.length <= berth.berthlength AND
      ((ships1.latitude - ports1.latitude) ^ 2 + (ships1.longitude - ports1.longitude) ^ 2) ^ 0.5 <= 1000

