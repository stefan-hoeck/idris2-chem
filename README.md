# idris2-chem : Dependently Typed Cheminformatics in Idris2

This is still WIP. Please come back later.

## About chem-inchi

In order to use the chem-inchi package, libinchi (version 1.07) must be installed. To do
this, either use your operating systems package manager, or clone the
[InChI GitHub repository](https://github.com/IUPAC-InChI/InChI), build the library
manually (for instance, by running `INCHI-1-SRC/INCHI_API/libinchi/gcc/run_make_on_linux.sh`),
and copy the resulting `.so` file to where your OS expects it (`/usr/lib` on arch Linux).
