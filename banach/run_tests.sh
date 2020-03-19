echo 'Start running some automated tests:'
cd lightweight-examples
for test in cats santa satellites ships pandemic TCP-H weather
do
    cd $test
    sh test.sh $test
    cd ..
done
cd ../..
echo 'Finished.'
