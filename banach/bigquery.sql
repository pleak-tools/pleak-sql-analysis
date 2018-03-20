feasible_ports =
SELECT ports.port_id AS id, ports.latitude AS latitude, ports.longitude AS longitude
FROM ports
WHERE ports.available

ship_distance_from_port = 
SELECT ships.ship_id AS ship_id, fports.id AS port_id,  ships.length AS length, ships.maxspeed AS speed,
       ((ships.latitude - fports.latitude) ^ 2 + (ships.longitude - fports.longitude) ^ 2) ^ 0.5 AS distance
FROM ships, feasible_ports AS fports

reachable_ports =
SELECT sdp1.port_id AS port_id, sdp1.ship_id AS ship_id
FROM ship_distance_from_port AS sdp1
WHERE sdp1.distance <= 1000

available_slots = 
SELECT sdp2.port_id AS port_id, sdp2.ship_id AS ship_id
FROM ship_distance_from_port AS sdp2, berth
WHERE berth.port_id = sdp2.port_id AND
      sdp2.length <= berth.berthlength

mintime =
SELECT min (sdp3.distance / sdp3.speed)
FROM ship_distance_from_port AS sdp3, available_slots, reachable_ports
WHERE sdp3.port_id = available_slots.port_id AND
      sdp3.ship_id = available_slots.ship_id AND
      sdp3.port_id = reachable_ports.port_id AND
      sdp3.ship_id = reachable_ports.ship_id
