#!/usr/bin/env bash

mkdir -vp build
sed -f "chem-data/elements.sed" "recources/elements.xml" > "build/elem.txt"
pack run chem-data
