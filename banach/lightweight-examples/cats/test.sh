../../dist/build/banach/banach -QDsa --db-create-tables cat_schema.sql cat_query.sql cat_constraints.att --epsilon 1.0 > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
