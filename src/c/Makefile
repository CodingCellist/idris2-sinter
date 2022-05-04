include ./common.mak

CC = clang
CFLAGS += -ggdb3 -O0
LDLIBS += -lgc

TRGT = test

default : all

all : $(TRGT)

$(TRGT) : test.o stdlib.o idris_sinter_stdlib.o

clean :
	$(RM) *.o *.ll $(TRGT)
