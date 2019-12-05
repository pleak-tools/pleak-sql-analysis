SELECT
    MIN ((ship.latitude ^ 2 + ship.longitude ^ 2) ^ 0.5 / ship.max_speed)
FROM
    ship
;
