CC=gcc
#DEBUG="-g"
CFLAGS = $(DEBUG) -O0 -DLINUX

OBJS = sendcap.o 
LIBS =  -lpcap -lnsl -lrt

all: ${OBJS}
	${CC} ${CFLAGS} -o sendcap ${OBJS} ${LIBS}

install:
	cp sendcap /usr/bin

clean:
	rm -f ${OBJS} sendcap

.c.o:
	${CC} ${CFLAGS} -c -o $*.o $<
