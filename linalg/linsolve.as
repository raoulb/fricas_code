-- aldor -ginterp -laldor -lalgebra linsolve.as
#include "aldor"
#include "algebra"
#pile

I ==> MachineInteger

Z ==> AldorInteger
Q ==> Fraction Z

VZ ==> Vector Z
VQ ==> Vector Q
MZ ==> DenseMatrix Z
MQ ==> DenseMatrix Q

LAQ ==> LinearAlgebra(Q, MQ)


import from I
import from Z, Q
import from VZ, VQ
import from MZ, MQ
import from LAQ


pm(M:DenseMatrix(Q)): () ==
    -- Pretty print dense matrices
    -- How make 'Q' just an arbitrary Ring?
    import from Character, String, TextWriter

    (nr, nc) := dimensions M

    for r in 1..nr repeat
        if r = 1 or r = nr then
            stdout << "+  ";
        else
            stdout << "|  ";
        for c in 1..nc repeat
            stdout << M(r,c);
            if c ~= nc then
                stdout << "   ";
        if r = 1 or r = nr then
            stdout << "  +" << newline;
        else
            stdout << "  |" << newline;


main(): () ==
    import from Character, String
    import from TextWriter

    n:I := 3
    stdout << "System size: " << n << newline

    -- q:Q := 8/4
    -- stdout << q << newline
    -- A:MQ := diagonal(q, n)
    -- A(1,3) := 3/2

    -- How to get a MQ w/o explicit annotation
    -- r1:VZ := [2, 3, 4]
    -- B:MZ := [r1, r1, r1]

    -- r1:VQ := [1/1, 2/1, 3/1]
    -- ambiguous operator / for 1/1

    -- r1:VQ := [2/2, 2/1, 3/1]
    -- r2:VQ := [4/1, 5/1, 6/1]
    -- r3:VQ := [7/1, 8/1, 9/1]
    -- A:MQ := [r1, r2, r3]
    -- A := transpose A

    A:MQ := [[2/1, 2/1, 3/1],
             [4/1, 5/1, 6/1],
             [7/1, 8/1, 9/1]]
    A := transpose A

    stdout << "Matrix A: " << A << newline

    (nr, nc) := dimensions A

    stdout << "Square: " << square? A << newline
    stdout << "Shape: " << "(" << nr << ", " << nc << ")" << newline
    stdout << "Rank: " << rank A << newline
    stdout << "Det: " << determinant A << newline

    -- b:MQ := zero(n, 1::I)
    -- b(1,1) := 8/2
    -- b(2,1) := 12/2
    -- b(3,1) := 16/2

    b:MQ := [[8/2],
             [12/2],
             [16/2]]
    b := transpose b

    stdout << "RHS b: " << b << newline

    (w, x, d) := solve(A, b)

    stdout << "x: " << x << newline
    stdout << "Is A x - b = 0? " << zero? (A*x-b) << newline

    stdout << "w: " << w << newline

    D:MQ := diagonal d
    stdout << "D: " << D << newline

    stdout << A*x << newline
    stdout << b*D << newline


    stdout << "A:" << newline
    pm(A)
    stdout << "b:" << newline
    pm(b)
    stdout << "x:" << newline
    pm(x)





main()
