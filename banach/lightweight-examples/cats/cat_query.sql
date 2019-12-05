SELECT
    count(*)
FROM
    cat
WHERE
    cat.available
    AND cat.color = 'black'
    AND cat.gender = 'male'
;
