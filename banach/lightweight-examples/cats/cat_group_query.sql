INSERT INTO catcounts SELECT
    cat.color AS catcolor,
    cat.gender AS catgender,
    count(*) AS cnt
FROM
    cat
WHERE
    cat.available
GROUP BY cat.color, cat.gender
;
INSERT INTO results SELECT
    sum(catfood.price * cc.cnt)
FROM
    catfood, catcounts AS cc
WHERE
    catfood.color = cc.catcolor
    AND cc.catgender = 'male'
;
