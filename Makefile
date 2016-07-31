TARGET=banach_tarski.vo

all: $(TARGET)

clean:
	rm -f *.glob *.vo .*.aux
	rm -f *.cm[iox] *.o *.cmxs *.native

.SUFFIXES: .v .vo

.v.vo:
	coqc $<
