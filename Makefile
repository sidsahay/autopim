CXX = clang

all: pimgen.so

CXXFLAGS = -rdynamic $(shell llvm-config --cxxflags) -g -O0

pimgen.o: pimgen.cpp

pimgen.so: pimgen.o
	$(CXX) -dylib -shared $^ -o $@


clean:
	rm -f *.o *~ *.so

.PHONY: clean all
