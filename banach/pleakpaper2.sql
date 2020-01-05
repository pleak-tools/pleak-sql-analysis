insert into port_enc select 
 port.port_id as port_id, 
  port.name as name, 
  port.latitude as latitude, 
  port.longitude as longitude, 
  port.offloadcapacity as offloadcapacity, 
  port.offloadtime as offloadtime, 
  port.harbordepth as harbordepth, 
  port.available as available
from port;

insert into aggr_count_enc select port.name AS name, count(*) as cnt
from ship, port_enc, port, ship_parameters
where port_enc.name = ship_parameters.portname
 	AND ((ship.latitude - port_enc.latitude) ^ 2 + (ship.longitude - port_enc.longitude) ^ 2) ^ 0.5 / ship.max_speed <= ship_parameters.deadline
    AND port.name = port_enc.name
group by port.name
;

insert into aggr_count select ac2.name as name,
       ac2.cnt as cnt 
from aggr_count_enc as ac2;

insert into capacities select count(slot.slot_id) as slots_number
 from port, aggr_count AS ac, slot, berth, ship_parameters
 where ac.name = ship_parameters.portname
 AND port.name = ship_parameters.portname
 AND port.port_id = berth.port_id
 AND slot.port_id = berth.port_id
 AND slot.berth_id = berth.berth_id 
 AND slot.slotstart <= ship_parameters.deadline
 AND slot.slotstart + port.offloadtime <= slot.slotend
 AND ac.cnt > 1
;
