SELECT DISTINCT ship.name, port.port_id, available_slots.berth_id, available_slots.slot_id,
    reachable_ports.arrival, available_slots.slotstart
  FROM reachable_ports, feasible_ports, port, 
    available_slots, berth, ship
  WHERE port.port_id = feasible_ports.port_id
    AND port.port_id = reachable_ports.port_id
    AND port.port_id = berth.port_id 
    AND available_slots.port_id = berth.port_id
    AND available_slots.berth_id = berth.berth_id
    AND ship.ship_id = available_slots.ship_id
    -- ship fits in berth
    AND berth.berthlength >= ship.length
    -- begin offload by deadline
    AND reachable_ports.arrival <= 10000 AND available_slots.slotstart <= 10000
    -- arrival AND available slot start + offloadtime before end of slot window
    AND reachable_ports.arrival + port.offloadtime <= available_slots.slotend
    AND available_slots.slotstart + port.offloadtime <= available_slots.slotend;
    
