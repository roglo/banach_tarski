TARGET=Banach_Tarski.vo
COQ_VERSION=`coqc -v | grep version | sed -e 's/^.*version //;s/[ ~].*$$//;s/\./_/g;s/^/COQ_/;s/+.*$$//'`

all: $(TARGET)

FILESFORDEP=`LC_ALL=C ls *.v`

clean:
	rm -f *.glob *.vo .*.aux
	rm -f *.vok *.vos
	rm -f *.cm[iox] *.o *.cmxs *.native
	rm -f .*.cache

depend:
	mv .depend .depend.bak
	coqdep -Q . . $(FILESFORDEP) | LC_ALL=C sort > .depend

show_coq_version:
	@echo $(COQ_VERSION)

.SUFFIXES: .v .vo .vp

%.vo: %.v
	rocq compile $<

%.v: %.vp
	@echo /lib/cpp -D$(COQ_VERSION) $< '>' $@
	@/bin/rm -f $@
	@sed -e 's|//|slsl|g' $< | \
	/lib/cpp -D$(COQ_VERSION) 2>/dev/null | \
	sed -e 's|slsl|//|g' | \
	grep -v '^#' > $@

.PHONY: all clean depend

include .depend
