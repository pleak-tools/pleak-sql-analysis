insert into port_enc
select 
  port.port_id as port_id, 
  port.name as name, 
  port.latitude as latitude, 
  port.longitude as longitude, 
  port.offloadcapacity as offloadcapacity, 
  port.offloadtime as offloadtime,
  port.available as available
from port;

insert into aggr_count_enc
select port.name as name, count(ship.ship_id) as cnt
from ship, 
  port_enc,
  port,
  parameters 
where port_enc.name = parameters.portname
  and port_enc.name = port.name
  and ((ship.latitude - port_enc.latitude)^2 + (ship.longitude - port_enc.longitude)^2) ^ 0.5 / ship.max_speed <= parameters.deadline 
group by port.name;

insert into aggr_count
select ac2.name as name, 
  ac2.cnt as cnt
from aggr_count_enc as ac2;

insert into capacities
select port.name as portname,
       count(slot.slot_id) as slots_number
from port, slot, berth, parameters
where port.name = parameters.portname
   AND port.port_id = berth.port_id
   AND slot.port_id = berth.port_id
   AND slot.berth_id = berth.berth_id 
   AND slot.slotstart <= parameters.deadline
   AND slot.slotstart + port.offloadtime <= slot.slotend
group by port.name;

insert into ship_count
SELECT
   ac.name as name,
   least(ac.cnt, cp.slots_number) as num_of_ships
from aggr_count AS ac, capacities AS cp, parameters
 where ac.name = cp.portname
 and ac.name = parameters.portname
;

SELECT
   port.name as name,
   MAX(sc.num_of_ships) as num_of_ships
from ship_count as sc, port
 where sc.name = port.name
 group by port.name
;
