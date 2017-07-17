TARGET=Banach_Tarski.vo
COQ_VERSION=`coqc -v | grep version | sed -e 's/^.*version //;s/[ ~].*$$//;s/\./_/g;s/^/COQ_/'`

all: $(TARGET)

FILESFORDEP=`LC_ALL=C ls *.v`

clean:
	rm -f *.glob *.vo .*.aux
	rm -f *.cm[iox] *.o *.cmxs *.native
	rm -f .*.cache
	rm -f MiscReals.v MiscTrigo.v RnCountable.v Banach_Tarski.v

depend:
	mv .depend .depend.bak
	coqdep -Q . . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo .vp

.v.vo:
	coqc $<

.vp.v:
	@echo $@ $(COQ_VERSION)
	@/bin/rm -f $@
	@sed -e 's|//|slsl|g' $< | \
	/lib/cpp -D$(COQ_VERSION) 2>/dev/null | \
	sed -e 's|slsl|//|g' | \
	grep -v '^#' > $@
	@chmod -w $@

.PHONY: all clean depend

include .depend
