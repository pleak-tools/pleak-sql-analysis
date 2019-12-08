SELECT
(weather.high_F approx 1 OR weather.high_C approx 1) AND (weather.low_F approx 1 OR weather.low_C approx 1)
FROM weather;
