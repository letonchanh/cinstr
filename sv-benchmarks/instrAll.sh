#!/bin/sh
printHelp(){
    echo "-h: help"
    echo "-s: Please specify your source program directory."
    exit -1
}

while getopts "hs:" arg
do
    case $arg in
        h) printHelp
           ;;
        s)
            cdir=$OPTARG
            ;;
    esac
done

for file in `ls $cdir/*cbe.c`; do
    echo $file
    ./instr.native -d $file
done
