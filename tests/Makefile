test: testbin
	./build/exec/runtests idris2 --interactive --failure-file failures

retest: testbin
	./build/exec/runtests idris2 --interactive --failure-file failures --only-file failures

testbin:
	idris2 --build tests.ipkg
