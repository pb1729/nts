./nts $1.nts $1.ll &&
llvm-as $1.ll &&
llvm-link $1.bc -o $1.bc &&
llc -filetype=obj $1.bc &&
gcc $1.o -o $1
