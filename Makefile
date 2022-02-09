SRCDIR = src
IDRIS = idris2
SIDRIS = $(PWD)/build/exec/main
DEPS = -p idris2 -p contrib -p network
SRCS = $(wildcard $(SRCDIR)/*.idr)
TRGT = sinter-idris2

all: $(TRGT)

check: $(SRCS)
	cd $(SRCDIR)
	$(IDRIS) $(DEPS) --check $^

$(TRGT): $(SRCS)
	$(IDRIS) --build Sinter.ipkg

gold: $(SRCS)
	$(SIDRIS) --build Sinter.ipkg

.PHONY: all clean

clean:
	$(RM) -r build $(SRCDIR)/build depends

