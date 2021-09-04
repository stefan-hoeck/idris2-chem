export IDRIS2 ?= idris2

lib_pkg = chem.ipkg

.PHONY: all lib install install-with-src clean clean-install repl develop

all: lib

clean-install: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

docs:
	${IDRIS2} --build ${docs_pkg}

install:
	${IDRIS2} --install ${lib_pkg}

install-with-src:
	${IDRIS2} --install-with-src ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${docs_pkg}
	${RM} -r build

# Start a REPL in rlwrap
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/Chem.idr

develop:
	find -name "*.idr" | entr -d idris2 --typecheck ${lib_pkg}
