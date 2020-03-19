../../dist/build/banach/banach -QDsa --db-create-tables satellite_schema.sql satellite_query.sql satellite_constraints.att --epsilon 1.0 --beta 0.001 --sigmoid-precision=0.001 > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
