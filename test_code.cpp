#include <stdlib.h>

// a file with test code, to see what corresponding llvm ir looks like
// compile with: clang -S -emit-llvm test_code.cpp

int a[12];

int main() {
  int b[10][20];
  int *c = (int *)malloc(43 * sizeof(int));
  return 0;
}

