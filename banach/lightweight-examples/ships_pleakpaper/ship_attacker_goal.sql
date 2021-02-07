SELECT
    (ship.longitude, ship.latitude) 
    approxWrtLp(2) 5
FROM ship
WHERE name = 'kohuke';
;
