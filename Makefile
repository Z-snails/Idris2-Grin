include config.mk

.PHONY : self-host install run typecheck clean build grin install-grin grinIdris2

$(IDRISGRIN) : ./src/**/*.idr $(PACKAGE)
	$(IDRIS) --build $(PACKAGE)

self-host : ./src/**/*.idr $(PACKAGE) $(IDRISGRIN)
	$(IDRISGRIN) --build $(PACKAGE)

run : $(IDRISGRIN)
	$(IDRISGRIN)

run-rl : $(IDRISGRIN)
	rlwrap $(IDRISGRIN)

typecheck :
	$(IDRIS) --typecheck $(PACKAGE)

clean :
	$(IDRIS) --clean $(PACKAGE)
	$(MAKE) -C grin clean

build :
	$(IDRIS) --build $(PACKAGE)

build-grinpkg :
	$(MAKE) -C grin build

install-grinpkg :
	$(MAKE) -C grin install

grinpkg : build-grinpkg install-grinpkg

sep :
	$(IDRIS) --build $(PACKAGE) --cg chez-sep

grinIdris2 :
	$(MAKE) -C grinIdris2 install