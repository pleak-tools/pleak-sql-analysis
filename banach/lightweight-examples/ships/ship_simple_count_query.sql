select count(*) as cnt
  from ship, port, ship_parameters
  where port.name = ship_parameters.portname
  AND (point(ship.latitude, ship.longitude) <@> point(port.latitude,
port.longitude)) / ship.max_speed <= ship_parameters.deadline
;
