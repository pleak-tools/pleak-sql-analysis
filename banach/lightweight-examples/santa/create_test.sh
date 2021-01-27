sh test_script.sh > test_result.txt  2> tmperr
rm tmperr
echo $1' test created'
