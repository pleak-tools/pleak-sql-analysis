echo 'Start creating some automated tests.'
echo 'NB! Do not commit the modified files "test_result.txt" if executed by mistake!'
cd lightweight-examples
for test in cats santa satellites ships ships_pleakpaper pandemic TCP-H weather
do
    cd $test
    sh create_test.sh $test
    cd ..
done
cd ../..
echo 'Finished.'
