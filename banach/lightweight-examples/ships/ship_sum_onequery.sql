INSERT INTO aggr_count SELECT
    SUM(ship.ship_id)
FROM
    port, slot, berth, ship, ship_parameters
WHERE
    port.name = ship_parameters.portname
    AND port.harbordepth >= ship.draft
    AND port.offloadcapacity >= ship.cargo
    AND port.port_id = berth.port_id
    AND slot.port_id = berth.port_id
    AND slot.berth_id = berth.berth_id
    AND berth.berthlength >= ship.length
    AND slot.slotstart <= ship_parameters.deadline
    AND slot.slotstart + port.offloadtime <= slot.slotend
    AND ((ship.latitude - port.latitude) ^ 2 + (ship.longitude - port.longitude) ^ 2) ^ 0.5 / ship.max_speed < 10
;
