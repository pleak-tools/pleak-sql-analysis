echo 'The next test takes a bit more time. Please wait...'
../../dist/build/banach/banach -QDsa --db-create-tables tcph_int_schema.sql bench1_1.sql tcph_constraints.att --epsilon 1.0 --beta 0.1 -d '|' > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1'test FAILED'
rm tmp
rm tmperr
