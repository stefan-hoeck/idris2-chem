#!/usr/bin/env bash

mkdir -vp build
sed -nf "chem-data/elements.sed" "resources/elements.xml" > "build/elem.txt"
pack run chem-data
