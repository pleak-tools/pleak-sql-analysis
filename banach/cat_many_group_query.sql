INSERT INTO count_cat_groups SELECT
    cat.color AS catcolor,
    cat.gender AS catgender,
    count(*) AS cnt
FROM
    cat
WHERE
    cat.available
GROUP BY cat.color, cat.gender
;

INSERT INTO estimate_food_price SELECT
    catfood.color AS group_catcolor,
    sum(catfood.price * cc.cnt)
FROM
    catfood, cat, count_cat_groups AS cc
WHERE
    catfood.color = cc.catcolor
    GROUP BY catfood.color
;
