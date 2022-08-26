include ./common.mak

CC = clang
CFLAGS += -ggdb3 -O0
LDLIBS += -lgc

TRGT = program

default : all

all : $(TRGT)

$(TRGT) : program.o stdlib.o idris_sinter_stdlib.o

clean :
	$(RM) *.o *.ll $(TRGT)
