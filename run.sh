clang -Xclang -disable-O0-optnone -O0 -emit-llvm -c $1.c -o $1.bc
opt -mem2reg $1.bc -o $1-m2r.bc
opt -indvars $1-m2r.bc -o $1-indvars.bc
opt -load ./autopim.so -autopim $1-indvars.bc -o out.bc
