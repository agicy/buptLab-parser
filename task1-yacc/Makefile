YACC := bison
YACCFLAGS := \
	--language=C \
	--no-lines \
	--token-table \
	--yacc \
	--header=build/yacc.h \
	--report=all \
	--report-file=build/yacc_report \
	--output=build/yacc.c \
	--graph=build/yacc.dot \
	--html=build/yacc.html \
	--xml=build/yacc.xml \

C := gcc
CFLAGS := \
	-O2 \
	-static \
	-DNDEBUG \
	-o build/main \
	-lm \

TESTCASES := $(wildcard test/testdata*.in)

main:
	mkdir -p build
	$(YACC) src/main.y $(YACCFLAGS)
	$(C) build/yacc.c $(CFLAGS)

test: main
	@$(foreach input_file, $(TESTCASES), \
		echo "\nRunning test: $(input_file)"; \
		output_file=build/$(notdir $(input_file:.in=.out)); \
		answer_file=test/$(notdir $(input_file:.in=.ans)); \
		echo "\tInput file:\t\t$(input_file)"; \
		echo "\tOutput file:\t\t$$output_file"; \
		echo "\tAnswer file:\t\t$$answer_file"; \
		/usr/bin/time -f "\tElapsed time:\t\t%E\n\tMaximum RSS:\t\t%M KiB" ./build/main < $(input_file) > $$output_file; \
		diff $$output_file $$answer_file -b || exit 1; \
		echo "Test $(input_file) passed"; \
	)

clean:
	$(RM) build/main build/main.c build/*.out
