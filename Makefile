TARGET=banach_tarski.vo

all: $(TARGET)

FILESFORDEP=`LC_ALL=C ls *.v`

clean:
	rm -f *.glob *.vo .*.aux
	rm -f *.cm[iox] *.o *.cmxs *.native

depend:
	mv .depend .depend.bak
	coqdep -Q . . $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

.PHONY: all clean depend

include .depend
