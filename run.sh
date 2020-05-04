clang -Xclang -disable-O0-optnone -O0 -emit-llvm -c $1.c -o $1.bc
#opt -mem2reg $1.bc -o $1-m2r.bc
opt -load ./pimgen.so -pimgen $1.bc -o out.bc
