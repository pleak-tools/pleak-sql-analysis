../../dist/build/banach/banach -QDsa --db-create-tables pandemic_schema.sql pandemic_groupquery.sql pandemic_constraints.att --epsilon 1.0 --beta 0.0 -d ',' --datestyle=US > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
