idris2 = idris2
target = idris2grin
builddir = ./build/exec
idris2grin = $(builddir)/$(target)

.PHONY : self-host install run clean

$(idris2grin) : ./src/**/*.idr idris2grin.ipkg
	$(idris2) --build idris2grin.ipkg

self-host : ./src/**/*.idr idris2grin.ipkg $(idris2grin)
	$(idris2grin) --build idris2grin.ipkg

install : $(idris2grin)
	$(idris2) --install idris2grin.ipkg

run : $(idris2grin)
	$(idris2grin)

clean :
	rm -rf ./build/
	rm -rf ./.output