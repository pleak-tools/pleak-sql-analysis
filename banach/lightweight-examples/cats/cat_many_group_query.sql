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

INSERT INTO prices SELECT
    catfood.color AS group_catcolor,
    min(catfood.price * cc.cnt)
FROM
    catfood, catcounts AS cc
WHERE
    catfood.color = cc.catcolor
    GROUP BY catfood.color
;
