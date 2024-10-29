JAVACC := javacc
JAVAC := javac
JAVA := java

TESTCASES := $(wildcard test/testdata*.in)

main:
	mkdir -p build
	cp src/main.jj build/main.jj
	cd build/ && $(JAVACC) main.jj && $(JAVAC) Calc.java

test: main
	@$(foreach input_file, $(TESTCASES), \
		echo "\nRunning test: $(input_file)"; \
		output_file=build/$(notdir $(input_file:.in=.out)); \
		answer_file=test/$(notdir $(input_file:.in=.ans)); \
		echo "\tInput file:\t\t$(input_file)"; \
		echo "\tOutput file:\t\t$$output_file"; \
		echo "\tAnswer file:\t\t$$answer_file"; \
		/usr/bin/time -f "\tElapsed time:\t\t%E\n\tMaximum RSS:\t\t%M KiB" $(JAVA) -classpath ./build Calc < $(input_file) > $$output_file; \
		diff $$output_file $$answer_file -b || exit 1; \
		echo "Test $(input_file) passed"; \
	)

clean:
	$(RM) build/*
