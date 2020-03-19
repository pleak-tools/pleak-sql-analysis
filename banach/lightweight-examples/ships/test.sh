../../dist/build/banach/banach -QDsa --db-create-tables ship_schema.sql ship_max_onequery.sql ship_constraints.att --policy=ship_attacker_goal.sql --epsilon 1.0 --beta 0.1 > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
