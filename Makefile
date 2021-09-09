export IDRIS2 ?= idris2

lib_pkg = chem.ipkg

doc_pkg = doc.ipkg


.PHONY: all
all: lib

.PHONY: clean-install
clean-install: clean install

.PHONY: clean-install-with-src
clean-install-with-src: clean install-with-src

.PHONY: lib
lib:
	${IDRIS2} --build ${lib_pkg}

.PHONY: docs
docs:
	${IDRIS2} --typecheck ${doc_pkg}

.PHONY: install
install:
	${IDRIS2} --install ${lib_pkg}

.PHONY: install-with-src
install-with-src:
	${IDRIS2} --install-with-src ${lib_pkg}

.PHONY: clean
clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${doc_pkg}
	${RM} -r build

# Start a REPL in rlwrap
.PHONY: repl
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/Chem.idr

.PHONY: develop
develop:
	find -name "*.idr" | entr -d idris2 --typecheck ${lib_pkg}
