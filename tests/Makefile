INTERACTIVE ?= --interactive

test: testbin
	./build/exec/runtests idris2 ${INTERACTIVE} --failure-file failures --only $(only)

retest: testbin
	./build/exec/runtests idris2 --interactive --failure-file failures --only-file failures

testbin:
	idris2 --build tests.ipkg

clean:
	idris2 --clean tests.ipkg
