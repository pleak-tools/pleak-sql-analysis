SELECT
  ship.ship_id exact AND
  (ship.longitude, ship.latitude) approxWrtLp(2) 5
FROM ship
WHERE cargo < 50
;
