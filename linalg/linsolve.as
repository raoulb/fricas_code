-- aldor -ginterp -laldor -lalgebra linsolve.as
#include "aldor"
#include "algebra"
#pile

I ==> MachineInteger

Z ==> AldorInteger
Q ==> Fraction Z

VQ ==> Vector Q
MQ ==> DenseMatrix Q

LAQ ==> LinearAlgebra(Q, MQ)


import from I
import from Z
import from Q
import from MQ
import from LAQ


main(): () ==
    import from Character, String
    import from TextWriter

    n:I := 3
    stdout << "System size: " << n << newline

    q:Q := 8/4
    stdout << q << newline

    A:MQ := diagonal(q, n)
    A(1,3) := 3/2

    stdout << "Matrix A: " << A << newline

    (nr, nc) := dimensions A

    stdout << "Square: " << square? A << newline
    stdout << "Shape: " << "(" << nr << ", " << nc << ")" << newline
    stdout << "Rank: " << rank A << newline
    stdout << "Det: " << determinant A << newline

    b:MQ := zero(n, 1::I)

    b(1,1) := 8/2
    b(2,1) := 12/2
    b(3,1) := 16/2

    stdout << "RHS b: " << b << newline

    (w, x, d) := solve(A, b)

    stdout << "w: " << w << newline
    stdout << "x: " << x << newline

    D:MQ := diagonal d

    stdout << "D: " << D << newline

    stdout << A*x << newline
    stdout << b*D << newline

    stdout << "Is A x - b = 0? " << zero? (A*x-b) << newline




main()
