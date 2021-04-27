IDRIS = idris2 -p idris2 -p contrib -p network
TRGT = sinter-idris2

all: $(TRGT)

check: $(TRGT)
	$(IDRIS) --check $^

$(TRGT): Sinter.idr
	$(IDRIS) $^ -o $@

.PHONY: all clean

clean:
	$(RM) -r build

