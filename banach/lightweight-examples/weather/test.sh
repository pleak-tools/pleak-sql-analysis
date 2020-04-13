../../dist/build/banach/banach -QDsa --db-create-tables weather_schema.sql weather_query.sql weather_constraints.att --epsilon 1.0 --beta 0.0 --delimiter ',' > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
