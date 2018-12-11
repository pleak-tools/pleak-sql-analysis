INSERT INTO catcounts SELECT
    cat.color AS groupid,
    count(*) AS cnt
FROM
    cat
WHERE
    cat.available
GROUP BY cat.color
;
INSERT INTO results SELECT
    sum(catfood.price * catcounts.cnt)
FROM
    catfood, catcounts
WHERE
    catfood.color = catcounts.groupid
;
