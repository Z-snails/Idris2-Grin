IDRIS2_LIBDIR = $(shell idris2 --libdir)

.PHONY: support
support:
	$(MAKE) -C support

.PHONY: install-support
install-support:
	mkdir $(IDRIS2_LIBDIR)/support/grin
	install support/libidris2Grinsupport.so $(IDRIS2_LIBDIR)/support/grin/

.PHONY: grin
grin:
	idris2 --build grin/grin.ipkg
	mkdir -p depends/grin-0
	cp -r grin/build/ttc/* depends/grin-0

.PHONY: idris2grin
idris2grin: grin
	idris2 --build idris2grin.ipkg
