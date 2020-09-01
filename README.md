# nts
A programming language with an elegant notation for tensor operations. Written using llvm.

**Example code:**

Matrix multiplication:
```lisp
(do
  (make (int 4 5) A)
  (<- (A i j) (+ 4 (* i j)))[i j]
  (make (int 5)   v)
  (<- (v i) (/ 360 i))[i]
  (make (int 4)   x)
  (<- (x i) (sum (j) (* (A i j) (v j))))[i]
)
```

**Limitations:**
* Unstable. This language is not ready to use in production.
* The language performs some type checks, but not all the ones that it should. Many type errors will not be caught (or will only be caught by llvm).
* Does not yet include floating point numbers.
* Does not yet include tensor expressions.
