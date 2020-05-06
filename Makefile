CXX = clang

all: autopim.so

CXXFLAGS = -rdynamic $(shell llvm-config --cxxflags) -g -O0

autopim.o: autopim.cpp

autopim.so: autopim.o
	$(CXX) -dylib -shared $^ -o $@

clean:
	rm -f *.o *~ *.so

.PHONY: clean all
