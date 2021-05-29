build:
	idris2 --build free.ipkg

install:
	idris2 --install free.ipkg

test: install
	make -C tests test

retest:
	make -C tests retest

clean:
	idris2 --clean free.ipkg
	make -C tests clean