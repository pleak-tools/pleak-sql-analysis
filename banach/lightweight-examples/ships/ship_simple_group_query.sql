select 
   port.port_id AS port_id,
   count(*) as cnt
from ship, port, ship_parameters
where
  (point(ship.latitude, ship.longitude) <@> point(port.latitude, port.longitude)) / ship.max_speed <= ship_parameters.deadline
group by port.port_id
;
