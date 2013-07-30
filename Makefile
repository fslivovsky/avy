
all: mc

mc: AbcMcInterface.o ClsItpSeqMc.o main.o
	g++ -g -o mc ClsItpSeqMc.o AbcMcInterface.o main.o libabc.a -DLIN64 -lm -rdynamic -lreadline -ltermcap -lpthread

AbcMcInterface.o:
	g++ -Wall -g -c AbcMcInterface.cc -o AbcMcInterface.o -I../abc/src/ -DLIN64

ClsItpSeqMc.o:
	g++ -Wall -g -c ClsItpSeqMc.cc -o ClsItpSeqMc.o -I../abc/src/ -DLIN64

main.o:
	g++ -Wall -g -c main.cc -o main.o -I../abc/src/ -DLIN64

clean:
	rm -rf *.o mc
