idris2 = idris2
target = idris2grin
builddir = ./build/exec
idris2grin = $(builddir)/$(target)

.PHONY: build install run clean

build: ./src/**/*.idr
	$(idris2) --build idris2grin.ipkg

install: build
	$(idris2) --install idris2grin.ipkg

run: build
	$(idris2grin)

clean:
	rm -rf ./build/
	rm -rf ./.output