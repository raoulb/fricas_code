-- This file shows some really nontrivial examples
--
-- Source: "A Rule-Based Component-Free Vector Algebra Package"
-- by Songxin Liang and  David J. Jeffrey
--
-- Individual examples:
-- J. Cunningham. "Vectors", Heinemann Educational Books Ltd, London, 1969
-- E. M. Patterson, "Solving Problems in Vector Algebra", Oliver & Boyd Ltd, Edinburgh-London, 1968
-- D. R. Stoutemyer, "Symbolic computer vector analysis", Computers & Mathematics with Applications, 1979

#include "algebra"
#include "aldorinterp"
#include "aldorio"

#library VA "vectorAlg.ao"

#pile

I ==> Integer

import from VA;
import from String, Symbol, I, VectorAlg I;

a := vector(-"a")
b := vector(-"b")
c := vector(-"c")
d := vector(-"d")
e := vector(-"e")
f := vector(-"f")
g := vector(-"g")
h := vector(-"h")

stdout << "Example 1 (Stoutemyer):" << newline

u14 := ((a^b)^(b^c)).(c^a)-(a.(b^c))*(a.(b^c))
u14s := simplify(u14)
stdout << u14 << newline
stdout << u14s << newline

stdout << "Example 2 (Stoutemyer):" << newline

u15 := (a-d)^(b-c)+(b-d)^(c-a)+(c-d)^(a-b)-2*(a^b+b^c+c^a)
u15s := simplify(u15)
stdout << u15 << newline
stdout << u15s << newline

u16 := (b^c)^(a^d)+(c^a)^(b^d)+(a^b)^(c^d)+2*s3p(a,b,c)*d
u16s := simplify(u16, true)
stdout << u16 << newline
stdout << u16s << newline

stdout << "Example 3 (Cunningham):" << newline

u18 := a^(b^c)+b^(c^a)+c^(a^b)
u18s := simplify(u18)
stdout << u18 << newline
stdout << u18s << newline

u19lhs := a^(b^(c^d))+b^(c^(d^a))+c^(d^(a^b))+d^(a^(b^c))
u19rhs := (a^c)^(b^d)
u19 := u19lhs = u19rhs
stdout << u19lhs << " = " << u19rhs << newline
stdout << u19 << newline

stdout << "Example 4 (Patterson):" << newline

u20 := (b^c).(a^d)+(c^a).(b^d)+(a^b).(c^d)
u20s := simplify(u20)
stdout << u20 << newline
stdout << u20s << newline

u21 := ((a^b)^c)^d+((b^a)^d)^c+((c^d)^a)^b+((d^c)^b)^a
u21s := simplify(u21)
stdout << u21 << newline
stdout << u21s << newline
