SELECT
    AVG(weather.high_C)
FROM
    weather
WHERE
    weather.state = 'California'
;
