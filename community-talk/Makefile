
.PHONY: run-%
run-%: %.out
	@echo "running $?"
	@./$?

%.out: %.grin
	grin --c-file rts.c --optimize --output-dir $(basename $?) -o $@ $?

GRIN_FILES = $(wildcard *.grin)
BUILD_FOLDERS = $(GRIN_FILES:.grin=)
GRIN_OUT = $(GRIN_FILES:.grin=.out)

.PHONY: unboxing
unboxing:
	grin --output-dir unboxing --gub unboxing.grin --save-grin unboxing/gub.grin
	grin --output-dir unboxing --ar unboxing.grin --save-grin unboxing/ar.grin

.PHONY: clean
clean:
	-rm -r $(BUILD_FOLDERS)
	-rm $(GRIN_OUT)

.PHONY: slides
slides:
	marp slides.md
