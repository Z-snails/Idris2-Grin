IDRIS = idris2
TARGET = idris2grin
BUILDDIR = ./build/exec
IDRISGRIN = $(BUILDDIR)/$(TARGET)
PACKAGE = idris2grin.ipkg

.PHONY : self-host install run typecheck clean

$(IDRISGRIN) : ./src/**/*.idr $(PACKAGE)
	$(IDRIS) --build $(PACKAGE)

self-host : ./src/**/*.idr $(PACKAGE) $(IDRISGRIN)
	$(IDRISGRIN) --build $(PACKAGE)

install : $(IDRISGRIN)
	$(IDRIS) --install $(PACKAGE)

run : $(IDRISGRIN)
	$(IDRISGRIN)

typecheck :
	$(IDRIS) --typecheck $(PACKAGE)

clean :
	$(IDRIS) --clean $(PACKAGE)