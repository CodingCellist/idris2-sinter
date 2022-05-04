LLC ?= clang -c
SINC ?= sinc

# Alternative option for llc
# (this seems to cause issues related to PIE on some systems):
# LLC  ?= llc-10 -filetype obj

%.o: %.ll
	$(LLC) $(LLCFLAGS) -o $@ $<

%.ll: %.sin
	$(SINC) -l $(SINCFLAGS) -o $@ $<

%.dot: %.sin
	$(SINC) -g $(SINCFLAGS) -o $@ $<

%.svg: %.dot
	dot -Tsvg $< > $@
