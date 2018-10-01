#!/usr/bin/env bash
#set -x

comm=$(basename $0)
engine=${comm#run-}
echo "Run test cases using engine $engine."

for file in $(find -name "*.smt2")
do
    echo "------------- $file -----"
    z3 "fixedpoint.engine=$engine" -v:3 -T:30 "$file" > "$file.z3_$engine" 2>&1
    if [ $? -eq 0 ]
    then
        echo "  Success"
    else
        echo "  Failed"
        cat "$file.z3_$engine"
    fi
done

for file in $(find -name "*.muz")
do
    echo "------------- $file -----"
    z3 "fixedpoint.engine=$engine" -v:3 -T:30 "$file" > "$file.z3_$engine" 2>&1
    if [ $? -eq 0 ]
    then
        echo "  Success"
    else
        echo "  Failed"
        cat "$file.z3_$engine"
    fi
done

