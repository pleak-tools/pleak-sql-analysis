sh test_script.sh > tmp  2> tmperr
cmp --silent tmp test_result.txt && echo $1' test PASSED' || echo $1' test FAILED'
rm tmp
rm tmperr
