; ModuleID = 'my_module'
source_filename = "my_module"

declare i64 @putchar(i64)

define i64 @main() {
entry2:
  %calltmp = call i64 @affine(i64 -3, i64 9)
  %calltmp1 = call i64 @putchar(i64 %calltmp)
  ret i64 0
}

define i64 @affine(i64 %x, i64 %y) {
entry:
  %multmp = mul i64 4, %y
  %addtmp = add i64 %x, %multmp
  ret i64 %addtmp
}
