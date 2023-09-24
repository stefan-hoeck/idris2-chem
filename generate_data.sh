#!/usr/bin/env bash

mkdir -vp build
sed -nf "chem-data/elements.sed" "resources/elements.xml" > "build/elem.txt"
sed -nf "chem-data/isotopes.sed" "resources/isotopes.xml" > "build/isotopes.txt"
pack run chem-data
