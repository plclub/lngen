### Compiler command to use, not including linking options or where to
### put the final executable.  We enable a lot of warnings...

EXTRA_WARNINGS = -fwarn-incomplete-record-updates
COMPILER = ghc --make -Wall $(EXTRA_WARNINGS)

### Name of the final executable.

EXE_NAME = ../lngen

### Every file that the program depends on.

FILES = $(wildcard *.hs) $(wildcard *.lhs)

### The executable name for Haddock.

HADDOCK = haddock

### The directory where Haddock output should go.

DOC_DIR = html

############################################################################

.PHONY: all clean doc doc-full

all: $(EXE_NAME)

$(EXE_NAME): $(FILES)
	$(COMPILER) -o $(EXE_NAME) $(LINK_OPTS) Main.hs

clean:
	rm -f  *.hi *.o
	rm -f  *.css *.gif *.html *.js
	rm -f  $(EXE_NAME)
	rm -rf $(DOC_DIR)

doc: $(FILES)
	$(HADDOCK) --html --odir $(DOC_DIR) Main.hs

doc-full: $(FILES)
	$(HADDOCK) --html --ignore-all-exports --odir $(DOC_DIR) Main.hs
