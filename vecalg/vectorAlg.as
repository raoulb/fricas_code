-- Copyright (c) 2006, Songxin Liang
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
--
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * Neither the name of the <organization> nor the
--       names of its contributors may be used to endorse or promote products
--       derived from this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
-- ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
-- WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
-- DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
-- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
-- LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
-- ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
-- SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "algebra"
#include "aldorio"

macro
{
  MI == MachineInteger;
  TREE == ExpressionTree;
  TEXT == TextWriter;
}

define VectorSpcCategory(R:Join(ArithmeticType, ExpressionType), n:MI == 3): Category == with
{
  *: (R, %) -> %;
  *: (%, R) -> %;
  +: (%, %) -> %;
  -: (%, %) -> %;
  -:     % -> %;
  =: (%, %) -> Boolean;

  if R has Field then
    /: (%, R) -> %;

  default
  {
    import from R;
    (x:%)-(y:%):% == x+(-1)*y;
    (x:%)*(r:R):% == r*x;
    -(x:%):% == (-1)*x;

    if R has Field then
      (x:%) / (r:R) : % == (inv r) * x;
  }
}

define VectorAlgCategory(R:Join(ArithmeticType, ExpressionType)): Category == VectorSpcCategory(R) with
{
  vector:      Symbol -> %;
  scalarZero:  () -> %;
  vectorZero:  () -> %;
  realVector?: % -> Boolean;

  simplify:    (%, flag:Boolean == false) -> %;
  identity?:   (%, %) -> Boolean;

  s3p:   (%, %, %) -> %;
  *:     (%, %) -> %;
  apply: (%, %) -> %;
  ^:     (%, %) -> %;
  <<:    (TextWriter, %) -> TextWriter;

  if R has Field then
    -- This will fail of course if y is not a scalar quantity
    /: (x:%, y:%) -> %;

  default
  {
    s3p(x:%, y:%, z:%):% == apply(x^y, z);
  }
}

VectorAlg(R:Join(ArithmeticType, ExpressionType)): Join(ExpressionType, VectorAlgCategory R) == add
{
  Term == Record(coe:R, sca:List List String, vec:List String);
  Rep == List Term;

  scaTerm == Record(coe2:R, sca2:List List String);
  scaList == List scaTerm;
  mixTerm == Record(scal:scaList, vec2:List String);

  import from MI, R, Term, Rep, TEXT, TREE, String, Boolean;
  import from scaTerm, scaList, mixTerm;

  local szero?(xx:Term): Boolean == {xx.coe=0 and empty? xx.vec;}

  local vzero?(xx:Term): Boolean ==
  {
    s:String := "0";
    xx.vec=[s] or (xx.coe=0 and ~empty? xx.vec);
  }

  local append(l:List List String, r:List List String): List List String ==
  {
    tp:List List String := copy(l);
    append!(tp, r);
  }

  local append(l:List String, r:List String): List String ==
  {
    tp:List String := copy(l);
    append!(tp, r);
  }

  local append(l:Rep, r:Rep): Rep ==
  {
    tp:Rep := copy(l);
    append!(tp, r);
  }

  local append(l:scaList, r:scaList): scaList ==
  {
    tp:scaList := copy(l);
    append!(tp, r);
  }

  local simplify0(xx:Rep):Rep ==
  {
    l: List Term := empty;
    tf: MI := 0;
    for tx in xx repeat{
      szero? tx =>l := l;
      vzero? tx => tf := 1;
      l := cons(tx, l);
    }
    empty? l and tf=0 =>[[0, [], []]];
    empty? l and tf=1 =>[[0, [], ["0"]]];
    reverse! l;
  }

  vector(a:Symbol):% == {per [ [1, [], [name a]] ];}

  scalarZero():% == {per [ [0, [], []] ];}

  vectorZero():% == {per [ [0, [], ["0"]] ];}

  realVector?(x:%):Boolean ==
  {
    import from Boolean;
    xx := rep x;
    empty? xx => false;
    t:Boolean := true;
    for tx in xx repeat
    {
      if empty? tx.vec then
      {
        t := false;
        break;
      }
    }
    t;
  }

  (r:R) * (x:%): % ==
  {
    xx := rep x;
    xx := [[r*p.coe, p.sca, p.vec] for p in xx];
    per simplify0(xx);
  }

  (s:%) * (x:%): % ==
  {
    ss := rep s;
    xx := rep x;
    l:List Term := empty;
    for ts in ss repeat{
      assert(empty? ts.vec);
      for tx in xx repeat{
	-- assert(~empty? tx.vec);
        m := [ts.coe*tx.coe, append(ts.sca, tx.sca), tx.vec]@Term;
        l := cons(m, l);
      }
    }
    per simplify0 reverse! l;
  }

  if R has Field then
  {
    (x:%) / (s:%): % ==
    {
      realVector? s => {stdout << "Attempted division by non-scalar quantity!" << newline;
                        per [[0, [], []]];}
      -- TODO: For a working implementation we need to extend the normal form.
      per [[0, [], []]];
    }
  }

  (x:%) + (y:%): % ==
  {
    per append(rep x, rep y);
  }

  apply(x:%, y:%): % ==
  {
    ~realVector? x =>
    {stdout<<"The first argument is not really vector!"<<newline;
     per [[0, [], []]];}
    ~realVector? y =>
    {stdout<<"The second argument is not really vector!"<<newline;
     per [[0, [], []]];}
    xx := rep x;
    yy := rep y;
    l:List Term := empty;
    for tx in xx repeat{
      n1:MI := #tx.vec;
      for ty in yy repeat{
        n2:MI := #ty.vec;
        if n1=1 and n2=1 then
        {
          m := [tx.coe*ty.coe, cons([tx.vec(1), ty.vec(1)], append(tx.sca, ty.sca)), []]@Term;
          l := cons(m, l);
        }
        else if n1=1 and n2=2 then
        {
          m := [tx.coe*ty.coe, cons([tx.vec(1), ty.vec(1), ty.vec(2)], append(tx.sca, ty.sca)), []]@Term;
          l := cons(m, l);
        }
        else if n1=2 and n2=1 then
        {
          m := [tx.coe*ty.coe, cons([tx.vec(1), tx.vec(2), ty.vec(1)], append(tx.sca, ty.sca)), []]@Term;
          l := cons(m, l);
        }
        else if n1=2 and n2=2 then
        {
          tp1:List List String := [[tx.vec(1), ty.vec(1)], [tx.vec(2), ty.vec(2)]];
          tp2:List List String := [[tx.vec(1), ty.vec(2)], [tx.vec(2), ty.vec(1)]];
          m1 := [tx.coe*ty.coe, append(tp1, append(tx.sca, ty.sca)), []]@Term;
          m2 := [(-1)*tx.coe*ty.coe, append(tp2, append(tx.sca, ty.sca)), []]@Term;
          l := cons(m2, cons(m1, l));
        }
      }
    }
    per simplify0 reverse! l;
  }

  (x:%) ^ (y:%): % ==
  {
    ~realVector? x =>
    {stdout<<"The first argument is not really vector!"<<newline;
     per [[0, [], []]];}
    ~realVector? y =>
    {stdout<<"The second argument is not really vector!"<<newline;
     per [[0, [], []]];}
    xx := rep x;
    yy := rep y;
    l:List Term := empty;
    for tx in xx repeat{
      n1:MI := #tx.vec;
      for ty in yy repeat{
        n2:MI := #ty.vec;
        if n1=1 and n2=1 then
        {
          m := [tx.coe*ty.coe, append(tx.sca, ty.sca), append(tx.vec, ty.vec)]@Term;
          l := cons(m, l);
        }
        else if n1=1 and n2=2 then
        {
          m1 := [tx.coe*ty.coe, cons([tx.vec(1), ty.vec(2)], append(tx.sca, ty.sca)), [ty.vec(1)]]@Term;
          m2 := [(-1)*tx.coe*ty.coe, cons([tx.vec(1), ty.vec(1)], append(tx.sca, ty.sca)), [ty.vec(2)]]@Term;
          l := cons(m2, cons(m1, l));
        }
        else if n1=2 and n2=1 then
        {
          m1 := [tx.coe*ty.coe, cons([tx.vec(1), ty.vec(1)], append(tx.sca, ty.sca)), [tx.vec(2)]]@Term;
          m2 := [(-1)*tx.coe*ty.coe, cons([tx.vec(2), ty.vec(1)], append(tx.sca, ty.sca)), [tx.vec(1)]]@Term;
          l := cons(m2, cons(m1, l));
        }
        else if n1=2 and n2=2 then
        {
          m1 := [tx.coe*ty.coe, cons([tx.vec(1), tx.vec(2), ty.vec(2)], append(tx.sca, ty.sca)), [ty.vec(1)]]@Term;
          m2 := [(-1)*tx.coe*ty.coe, cons([tx.vec(1), tx.vec(2), ty.vec(1)], append(tx.sca, ty.sca)), [ty.vec(2)]]@Term;
          l := cons(m2, cons(m1, l));
        }
      }
    }
    per simplify0 reverse! l;
  }

  local writeTerm(port:TEXT, t:Term):() ==
  {
    szero? t => port<<0$R;
    vzero? t => port<<"O";
    if t.coe~=1 then port<<t.coe;
    tp := t.sca;
    while ~empty? tp repeat
    {
      t1 := first tp;
      tp := rest tp;
      if #t1=1 then port<<first t1;
      else if #t1=2 then
      {
        port<<"("<<t1(1)<<"."<<t1(2)<<")";
      }
      else
      {
        port<<"(";
        for s in t1 repeat port<<s;
        port<<")";
      }
    }
    if ~empty? t.vec then
    {
      if (t.coe~=1 or ~empty? t.sca) then port<<"*";
      #t.vec=1 => port<<first t.vec;
      port<<"("<<t.vec(1)<<"^"<<t.vec(2)<<")";
    }
  }

  (port:TEXT)<<(x:%):TEXT ==
  {
    xx := rep x;
    empty? xx => port<<0$R;

    if R has OrderedArithmeticType then
    {
      import from R pretend OrderedArithmeticType;
      tp := first xx;
      if tp.coe<0 then
      {
        port<<"-";
        writeTerm(port, [(-1)*tp.coe, tp.sca, tp.vec]@Term);
      }
      else
      { writeTerm(port, tp);}
      xx := rest xx;
      while ~empty? xx repeat
      {
        tx := first xx;
        xx := rest xx;
        if tx.coe<0 then
        {
          port<<"-";
          writeTerm(port, [(-1)*tx.coe, tx.sca, tx.vec]@Term);
        }
        else
        {
          port<<"+";
          writeTerm(port, tx);
        }
      }
    }
    else
    {
      writeTerm(port, first xx);
      xx := rest xx;
      while ~empty? xx repeat
      {
        tx := first xx;
        xx := rest xx;
        port<<"+";
        writeTerm(port, tx);
      }
    }
    port;
  }

  (x:%) = (y:%): Boolean ==
  {
    identity?(x, y);
  }

  extree(x:%):TREE ==
  {
    extree "0";
  }

  identity?(x:%, y:%): Boolean ==
  {
    z := simplify(x-y);
    zz := copy rep z;
    #zz=1 and (vzero?(first(zz)) or szero?(first(zz))) => true;

    l:List Term := empty;
    if #zz > 2 then
    {
      tt:Boolean := false;
      stp:List Term := empty;
      while ~same?(per zz, per stp) repeat
      {
        stp := copy zz;
        l := rule01(zz);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule01(zz, true);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule11(zz);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule02(zz);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule02(zz, true);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule03(zz);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule04(zz);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
        l := rule04(zz, true);
        tpz := simplify per l;
        tpzz := rep tpz;
        #tpzz=1 and (vzero?(first(tpzz)) or szero?(first(tpzz))) => {tt := true; break;}
        if #tpzz<#zz or #tpzz=#zz then zz := tpzz;
      }
      tt => tt;
      stdout<<per zz<<" = "<<"0 ??? "<<newline<<newline;
      tt;
    }
    else
    {
      stdout<<z<<" = "<<"0 ??? "<<newline<<newline;
      false;
    }
  }

  ---- The following programs deal with simplifications of vector expressions ----


  ---- Mathematically, "order" means "not greater" ----

  local listOrder?(l1:List String, l2:List String): Boolean ==
  {
    empty? l1 => true;
    empty? l2 => false;
    n1 := #l1;
    n2 := #l2;
    n1<n2 =>true;
    n1>n2 =>false;
    tt:Boolean := true;
    for i in 1..n1 repeat
    {
      l1(i)<l2(i) => { tt := true; break; }
      l1(i)>l2(i) => { tt := false; break; }
    }
    tt;
  }

  local listEq?(l1:List String, l2:List String): Boolean ==
  {
    empty? l1 => empty? l2;
    n1 := #l1;
    n2 := #l2;
    n1~=n2 => false;
    tt:Boolean := true;
    for i in 1..n1 repeat
    {
      l1(i)~=l2(i) => {tt := false; break; }
    }
    tt;
  }

  local dblListOrder?(l1:List List String, l2:List List String): Boolean ==
  {
    empty? l1 => true;
    empty? l2 => false;
    n1 := #l1;
    n2 := #l2;
    n1<n2 =>true;
    n1>n2 =>false;
    tt:Boolean := true;
    for i in 1..n1 repeat
    {
      listOrder?(l1(i), l2(i)) and ~listEq?(l1(i), l2(i)) =>{ tt := true; break; }
      ~listOrder?(l1(i), l2(i)) => { tt := false; break; }
    }
    tt;
  }

  local dblListEq?(l1:List List String, l2:List List String): Boolean ==
  {
    empty? l1 => empty? l2;
    n1 := #l1;
    n2 := #l2;
    n1~=n2 => false;
    tt:Boolean := true;
    for i in 1..n1 repeat
    {
      ~listEq?(l1(i), l2(i)) => {tt := false; break; }
    }
    tt;
  }

  local termOrder?(t1:Term, t2:Term): Boolean ==
  {
    szero? t1 or vzero? t1 => true;
    szero? t2 or vzero? t2 => false;
    listOrder?(t1.vec, t2.vec) and ~listEq?(t1.vec, t2.vec) => true;
    ~listOrder?(t1.vec, t2.vec) => false;
    dblListOrder?(t1.sca, t2.sca) and ~dblListEq?(t1.sca, t2.sca) =>true;
    ~dblListOrder?(t1.sca, t2.sca) => false;
    true;
  }

  local termEq?(t1:Term, t2:Term): Boolean ==
  {
    t1.coe=t2.coe and dblListEq?(t1.sca, t2.sca) and listEq?(t1.vec, t2.vec);
  }

  -- local permute4():List List MI ==
  -- {
  --   import from Set MI, List MI, List List MI;
  --   a:Set MI := [1, 2, 3, 4];
  --   out:List List MI := empty;
  --   for i in a repeat
  --   {
  --     for j in a-([i] @ Set MI) repeat
  --     {
  --       for k in a-([i, j] @ Set MI) repeat
  --       {
  --         for l in a-([i, j, k] @ Set MI) repeat
  --         {
  --           out := cons([i, j, k, l], out);
  --         }
  --       }
  --     }
  --   }
  --   out;
  -- }

  simplify(x:%, flag:Boolean == false):% ==
  {
    xx := copy rep x;
    empty? xx => x;
    lo:Rep := empty;

    for tx in xx repeat
    {
      tpx:Term := [tx.coe, copy tx.sca, copy tx.vec];
      #tpx.vec=2 and tpx.vec(1)=tx.vec(2) => lo := lo;
      if #tpx.vec=2 and tpx.vec(1)>tpx.vec(2) then
      {
        tpx.vec := [tpx.vec(2), tpx.vec(1)];
        tpx.coe := (-1)*tpx.coe;
      }
      empty? tpx.sca => lo := cons(tpx, lo);
      li:List List String := empty;
      for ts in tpx.sca repeat
      {
        n := #ts;
        n=1 => {li := cons(ts, li); }
        n=2 => {if ts(1)>ts(2) then { li := cons([ts(2), ts(1)], li); } else {li := cons(ts, li);} }
        n=3 =>
        {
          if ts(1)=ts(2) or ts(2)=ts(3) or ts(3)=ts(1) then {tpx.coe := 0; li := tpx.sca; break; }
          else
          {
            tp:List String := empty;
            ms := min(min(ts(1), ts(2)), ts(3));
            (ll, nn) := find(ms, ts);
            if nn=1 then { tp := ts; }
            else if nn=2 then { tp := [ts(2), ts(3), ts(1)]; }
            else if nn=3 then { tp := [ts(3), ts(1), ts(2)]; }
            if tp(2)>tp(3) then
            {
              tp := [tp(1), tp(3), tp(2)];
              tpx.coe := -tpx.coe;
            }
            li := cons(tp, li);
          }
        }
      }
      tpx.sca := sort!(li, listOrder?);
      lo := cons(tpx, lo);
    }
    lo := reverse lo;
    lo := simplify0(lo);
    empty? lo => per lo;
    yy:List Term := sort!(lo, termOrder?);
    lo := [first yy];
    yy := rest yy;
    for tx in yy repeat
    {
      t1 := first lo;
      listEq?(tx.vec, t1.vec) and dblListEq?(tx.sca, t1.sca) =>
        lo := cons([tx.coe+t1.coe, t1.sca, t1.vec], rest lo);
      lo := cons(tx, lo);
    }
    lo := reverse simplify0 lo;

    if flag and #lo>2 then
    {
      stp:List Term := empty;
      while ~same?(per lo, per stp) repeat
      {
        stp := copy lo;
        tpzz:List Term := rule01(lo);
        l:% := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule01(lo, true);
        l:% := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule11(lo);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule02(lo);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule02(lo, true);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule03(lo);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule04(lo);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
        tpzz := rule04(lo, true);
        l := simplify per tpzz;
        if #(rep l)<#lo or #(rep l)=#lo then lo := rep l;
        #lo<3 => break;
      }
      per lo;
    }
    else
    {
      per lo;
    }
  }


  ---- implementations of reasoning rules ----

  import from Set String;
  import from Set List String;
  import from List Set String;
  import from List Set List String;

  local setsGcd0 (lt:List Set String):Set String ==
  {
    #lt=1 => first lt;
    tp0 := first lt;
    rslt := rest lt;
    for tx in rslt repeat
    {
      tp := union(tp0, tx);
      tp := tp-(tp0-tx);
      tp := tp-(tx-tp0);
      tp0 := tp;
    }
    tp0;
  }

  local setsGcd (lt:List Set List String):Set List String ==
  {
    #lt=1 => first lt;
    tp0 := first lt;
    rslt := rest lt;
    for tx in rslt repeat
    {
      tp := union(tp0, tx);
      tp := tp-(tp0-tx);
      tp := tp-(tx-tp0);
      tp0 := tp;
    }
    tp0;
  }

  local extend? (xx:List Term):Boolean ==
  {
    realVector?(per xx) => false;
    tt:Boolean := true;
    n2:MI := 0;
    n3:MI := 0;
    for tx in xx repeat
    {
      tp := tx.sca;
      n := #tp;
      n<3 => {tt := false; break;}
      if #tp(n)=2
      then n2 := n2+1;
      else if #tp(n-1)=#tp(n) and #tp(n)=3
      then n3 := n3+1;
    }
    if n2<3 or n2<12*n3 then tt := false;
    tt;
  }

  local cond? (p1:scaTerm, p2:scaTerm, p3:scaTerm):Boolean ==
  {
    tt:Boolean := (p1.coe2=p2.coe2 or p1.coe2=(-1)*p2.coe2);
    tt := tt and (p2.coe2=p3.coe2 or p2.coe2=(-1)*p3.coe2);
    tt := tt and (p3.coe2=p1.coe2 or p3.coe2=(-1)*p1.coe2);
    ~tt => false;
    l1 := p1.sca2 pretend Set List String;
    l2 := p2.sca2 pretend Set List String;
    l3 := p3.sca2 pretend Set List String;
    sg := setsGcd([l1, l2, l3]);
    s1 := (l1-sg) pretend List List String;
    s2 := (l2-sg) pretend List List String;
    s3 := (l3-sg) pretend List List String;
    tt := #s1=2 and #s2=2 and #s3=2 and #s1(1)*#s1(2)=6;
    ~(tt and #s2(1)*#s2(2)=6 and #s3(1)*#s3(2)=6) => false;
    s1 := sort!(s1, listOrder?);
    s2 := sort!(s2, listOrder?);
    s3 := sort!(s3, listOrder?);
    t12 := s1(1) pretend Set String;
    t22 := s2(1) pretend Set String;
    t32 := s3(1) pretend Set String;
    t13 := s1(2) pretend Set String;
    t23 := s2(2) pretend Set String;
    t33 := s3(2) pretend Set String;
    ut2 := union(union(t12, t22), t32);
    ut3 := union(union(t13, t23), t33);
    it2:Set String := setsGcd0([t12, t22, t32]);
    it3:Set String := setsGcd0([t13, t23, t33]);
    tt := #ut2=4 and #ut3=4 and #it2=1 and #it3=1;
    ~(tt and (ut2-it2)=(ut3-it3) and #(ut2-it2)=3) => false;
    true;
  }

  -- we assume #pi.vec=2
  local cond11? (p1:Term, p2:Term, p3:Term):Boolean ==
  {
    tt:Boolean := (p1.coe=p2.coe or p1.coe=(-1)*p2.coe);
    tt := tt and (p2.coe=p3.coe or p2.coe=(-1)*p3.coe);
    tt := tt and (p3.coe=p1.coe or p3.coe=(-1)*p1.coe);
    ~tt => false;
    l1 := p1.sca pretend Set List String;
    l2 := p2.sca pretend Set List String;
    l3 := p3.sca pretend Set List String;
    sg := setsGcd([l1, l2, l3]);
    s1 := (l1-sg) pretend List List String;
    s2 := (l2-sg) pretend List List String;
    s3 := (l3-sg) pretend List List String;
    tt := #s1=1 and #s2=1 and #s3=1 and #s1(1)=#s2(1);
    ~(tt and #s2(1)=#s3(1) and #s3(1)=2) => false;
    t11 := s1(1) pretend Set String;
    t21 := s2(1) pretend Set String;
    t31 := s3(1) pretend Set String;
    t12 := p1.vec pretend Set String;
    t22 := p2.vec pretend Set String;
    t32 := p3.vec pretend Set String;
    ut1 := union(union(t11, t21), t31);
    ut2 := union(union(t12, t22), t32);
    it1:Set String := setsGcd0([t11, t21, t31]);
    it2:Set String := setsGcd0([t12, t22, t32]);
    ~(#it1=1 and #it2=0 and #ut2=3 and #setsGcd0([ut1, ut2])=3)=> false;
    true;
  }

  local distribute (p:mixTerm):List Term ==
  {
    l:List Term := empty;
    for tx in p.scal repeat
    {
      l := cons([tx.coe2, tx.sca2, p.vec2], l);
    }
    l;
  }

  local same?(x:%, y:%): Boolean ==
  {
    z := simplify(x-y);
    zz := rep z;
    #zz=1 and (vzero?(first(zz)) or szero?(first(zz))) => true;
    false;
  }

  local comb(p:mixTerm):List Term ==
  {
    l1 := (p.scal(1)).sca2 pretend Set List String;
    l2 := (p.scal(2)).sca2 pretend Set List String;
    l3 := (p.scal(3)).sca2 pretend Set List String;
    sg := setsGcd([l1, l2, l3]);
    s1 := (l1-sg) pretend List List String;
    s2 := (l2-sg) pretend List List String;
    s3 := (l3-sg) pretend List List String;

    s1 := sort!(s1, listOrder?);
    s2 := sort!(s2, listOrder?);
    s3 := sort!(s3, listOrder?);
    t12 := s1(1) pretend Set String;
    t22 := s2(1) pretend Set String;
    t32 := s3(1) pretend Set String;
    t13 := s1(2) pretend Set String;
    t23 := s2(2) pretend Set String;
    t33 := s3(2) pretend Set String;
    ut2 := union(union(t12, t22), t32);
    ut3 := union(union(t13, t23), t33);
    it2:Set String := setsGcd0([t12, t22, t32]);
    it3:Set String := setsGcd0([t13, t23, t33]);

    d := it2(1);
    h := it3(1);
    a := (ut2-it2)(1);
    b := (ut2-it2)(2);
    c := (ut2-it2)(3);
    lg := sg pretend List List String;
    coe:R := (p.scal(1)).coe2;

    tp1 := [coe, append([[d, a], [h, b, c]], lg), p.vec2]@Term;
    tp2 := [coe, append([[d, b], [a, h, c]], lg), p.vec2]@Term;
    tp3 := [coe, append([[d, c], [a, b, h]], lg), p.vec2]@Term;
    same? (per [tp1, tp2, tp3], per distribute p) =>
      [[coe, append([[d, h], [a, b, c]], lg), p.vec2]];

    tp1 := [coe, append([[h, a], [d, b, c]], lg), p.vec2]@Term;
    tp2 := [coe, append([[h, b], [a, d, c]], lg), p.vec2]@Term;
    tp3 := [coe, append([[h, c], [a, b, d]], lg), p.vec2]@Term;
    same? (per [tp1, tp2, tp3], per distribute p) =>
      [[coe, append([[h, d], [a, b, c]], lg), p.vec2]];

    tp1 := [coe, append([[d, a], [h, c, b]], lg), p.vec2]@Term;
    tp2 := [coe, append([[d, c], [a, h, b]], lg), p.vec2]@Term;
    tp3 := [coe, append([[d, b], [a, c, h]], lg), p.vec2]@Term;
    same? (per [tp1, tp2, tp3], per distribute p) =>
      [[coe, append([[d, h], [a, c, b]], lg), p.vec2]];

    tp1 := [coe, append([[h, a], [d, c, b]], lg), p.vec2]@Term;
    tp2 := [coe, append([[h, c], [a, d, b]], lg), p.vec2]@Term;
    tp3 := [coe, append([[h, b], [a, c, d]], lg), p.vec2]@Term;
    same? (per [tp1, tp2, tp3], per distribute p) =>
      [[coe, append([[h, d], [a, c, b]], lg), p.vec2]];

    distribute p;
  }

  -- we assume #pi.vec=2
  local comb11(p1:Term, p2:Term, p3:Term):List Term ==
  {
    l1 := p1.sca pretend Set List String;
    l2 := p2.sca pretend Set List String;
    l3 := p3.sca pretend Set List String;
    sg := setsGcd([l1, l2, l3]);
    s1 := (l1-sg) pretend List List String;
    s2 := (l2-sg) pretend List List String;
    s3 := (l3-sg) pretend List List String;
    t11 := s1(1) pretend Set String;
    t21 := s2(1) pretend Set String;
    t31 := s3(1) pretend Set String;
    t12 := p1.vec pretend Set String;
    t22 := p2.vec pretend Set String;
    t32 := p3.vec pretend Set String;
    ut2 := union(union(t12, t22), t32);
    it1:Set String := setsGcd0([t11, t21, t31]);
    d := it1(1);
    a := ut2(1);
    b := ut2(2);
    c := ut2(3);
    lg := sg pretend List List String;
    tp1 := [p1.coe, cons([d, a], lg), [b, c]]@Term;
    tp2 := [p1.coe, cons([d, b], lg), [c, a]]@Term;
    tp3 := [p1.coe, cons([d, c], lg), [a, b]]@Term;
    same? (per [tp1, tp2, tp3], per [p1, p2, p3]) =>
      [[p1.coe, cons([a, b, c], lg), [d]]];
    tp1 := [p1.coe, cons([d, a], lg), [c, b]]@Term;
    tp2 := [p1.coe, cons([d, b], lg), [a, c]]@Term;
    tp3 := [p1.coe, cons([d, c], lg), [b, a]]@Term;
    same? (per [tp1, tp2, tp3], per [p1, p2, p3]) =>
      [[p1.coe, cons([a, c, b], lg), [d]]];

    [p1, p2, p3];
  }

  ---- (abc)*d = (d.c)*(axb) + (d.a)*(bxc) + (d.b)*(cxa) ----

  local rule01(yy:List Term, flag:Boolean == false):List Term ==
  {
    #yy<3 => yy;
    ~realVector?(per yy) => yy;
    xx := copy yy;
    xx := sort!(xx, termOrder?);
    l:List Term := empty;
    for tx in xx repeat
    {
      if #tx.vec ~= 1 or empty? tx.sca then l := cons(tx, l);
      else
      {
        n := #tx.sca;
        lt:List String := empty;
        rt:List List String := empty;
        if flag then
        {
          lt := first reverse tx.sca;
          rt := rest reverse tx.sca;
        }
        else
        {
          for i in 1..n repeat
          {
            #tx.sca(i)=3 =>
            {
              lt := tx.sca(i);
              rt := append([tx.sca(j) for j in 1..(i-1)], [tx.sca(j) for j in (i+1)..n]);
              break;
            }
          }
        }
        d := first tx.vec;
        if #lt ~= 3 then l := cons(tx, l);
        else
        {
          l := cons([tx.coe, append(rt, [[d, lt(3)]]), [lt(1), lt(2)]], l);
          l := cons([tx.coe, append(rt, [[d, lt(1)]]), [lt(2), lt(3)]], l);
          l := cons([tx.coe, append(rt, [[d, lt(2)]]), [lt(3), lt(1)]], l);
        }
      }
    }
    l;
  }

  ---- (abc)*(dxh) = [(b.d)(c.h)-(b.h)(c.d)]*a + [(c.d)(a.h)-(c.h)(a.d)]*b + [(a.d)(b.h)-(a.h)(b.d)]*c ----

  local rule02(yy:List Term, flag:Boolean == false):List Term ==
  {
    #yy<3 => yy;
    ~realVector?(per yy) => yy;
    xx := copy yy;
    xx := sort!(xx, termOrder?);
    l:List Term := empty;
    for tx in xx repeat
    {
      if #tx.vec ~= 2 or empty? tx.sca then l := cons(tx, l);
      else
      {
        n := #tx.sca;
        lt:List String := empty;
        rt:List List String := empty;
        if flag then
        {
          lt := first reverse tx.sca;
          rt := rest reverse tx.sca;
        }
        else
        {
          for i in 1..n repeat
          {
            #tx.sca(i)=3 =>
            {
              lt := tx.sca(i);
              rt := append([tx.sca(j) for j in 1..(i-1)], [tx.sca(j) for j in (i+1)..n]);
              break;
            }
          }
        }
        d := tx.vec(1);
        h := tx.vec(2);
        if #lt ~= 3 then l := cons(tx, l);
        else
        {
          l := cons([tx.coe, append(rt, [[lt(2), d], [lt(3), h]]), [lt(1)]], l);
          l := cons([-tx.coe, append(rt, [[lt(2), h], [lt(3), d]]), [lt(1)]], l);
          l := cons([tx.coe, append(rt, [[lt(3), d], [lt(1), h]]), [lt(2)]], l);
          l := cons([-tx.coe, append(rt, [[lt(3), h], [lt(1), d]]), [lt(2)]], l);
          l := cons([tx.coe, append(rt, [[lt(1), d], [lt(2), h]]), [lt(3)]], l);
          l := cons([-tx.coe, append(rt, [[lt(1), h], [lt(2), d]]), [lt(3)]], l);
        }
      }
    }
    l;
  }

  ---- (d.a)(hbc) + (d.b)(ahc) + (d.c)(abh) = (d.h)(abc) ----

  local rule03(yy:List Term):List Term ==
  {
    xx := copy yy;
    #xx<3 => xx;
    xx := sort!(xx, termOrder?);
    tp00 := first xx;
    zz := rest xx;
    lo := [ [[[tp00.coe, tp00.sca]], tp00.vec] ]@List mixTerm;
    for tx in zz repeat
    {
      tp01 := first lo;
      listEq? (tp01.vec2, tx.vec) =>
        lo := cons([cons([tx.coe, tx.sca], tp01.scal), tp01.vec2], rest lo);
      lo := cons([[[tx.coe, tx.sca]], tx.vec], lo);
    }
    l:List Term := empty;
    for tx in lo repeat
    {
      L:scaList := tx.scal;
      n := #L;
      n<3 => l := append(l, distribute tx);
      ttp2:scaList := empty;
      for i in 1..n repeat
      {
        empty? L(i).sca2 or #(first (reverse L(i).sca2))<3 =>
          l := append(l, distribute [[L(i)], tx.vec2]);
        ttp2 := cons(L(i), ttp2);
      }
      L := ttp2;
      n := #L;
      tt:Boolean := false;
      ttp:scaList := empty;
      ttp0:scaList := empty;
      while n>2 repeat
      {
        for i in 1..(n-2) repeat
        {
          for j in (i+1)..(n-1) repeat
          {
            for k in (j+1)..n repeat
            {
              if cond? (L(i), L(j), L(k)) then
              {
                ttp := [L(i), L(j), L(k)];
                ttp0 := append([L(s) for s in 1..(i-1)], [L(s) for s in (i+1)..(j-1)]);
                ttp0 := append(ttp0, [L(s) for s in (j+1)..(k-1)]);
                ttp0 := append(ttp0, [L(s) for s in (k+1)..n]);
                L := ttp0;
                tt := true;
                break;
              }
            }
            if tt then break;
          }
          if tt then break;
        }
        empty? ttp => break;
        l := append(l, comb [ttp, tx.vec2]);
        ttp := empty;
        n := #L;
      }
      if ~empty? L then l := append(l, distribute [L, tx.vec2]);
    }
    l;
  }

  ---- (abc)(dgh) = [(bxc).(dxg)](a.h) + [(cxa).(dxg)](b.h) + [(axb).(dxg)](c.h) ----

  local rule04(yy:List Term, flag:Boolean == false):List Term ==
  {
    xx := copy yy;
    #xx<3 => xx;
    xx := sort!(xx, termOrder?);
    if extend?(xx) then xx := rep simplify per rule13(xx);
    l:List Term := empty;
    for tx in xx repeat
    {
      tp0 := tx.sca;
      n := #tp0;
      if n<2 then l := cons(tx, l);
      else
      {
        lt31:List String := empty;
        lt32:List String := empty;
        if flag then
        {
          lt31 := tp0(n-1);
          lt32 := tp0(n);
          rt:List List String := [tp0(j) for j in 1..(n-2)];
        }
        else
        {
          for i in 1..n-1 repeat
          {
            #tp0(i)=3 and #tp0(i+1)=3 =>
            {
              lt31 := tp0(i);
              lt32 := tp0(i+1);
              rt := append([tp0(j) for j in 1..(i-1)], [tp0(j) for j in (i+2)..n]);
              break;
            }
          }
        }
        if #lt31*#lt32 ~= 9 then l := cons(tx, l);
        else
        {
          l := cons([tx.coe, append(rt, [[lt31(2), lt32(1)], [lt31(3), lt32(2)], [lt31(1), lt32(3)]]), tx.vec], l);
          l := cons([-tx.coe, append(rt, [[lt31(2), lt32(2)], [lt31(3), lt32(1)], [lt31(1), lt32(3)]]), tx.vec], l);
          l := cons([tx.coe, append(rt, [[lt31(3), lt32(1)], [lt31(1), lt32(2)], [lt31(2), lt32(3)]]), tx.vec], l);
          l := cons([-tx.coe, append(rt, [[lt31(3), lt32(2)], [lt31(1), lt32(1)], [lt31(2), lt32(3)]]), tx.vec], l);
          l := cons([tx.coe, append(rt, [[lt31(1), lt32(1)], [lt31(2), lt32(2)], [lt31(3), lt32(3)]]), tx.vec], l);
          l := cons([-tx.coe, append(rt, [[lt31(1), lt32(2)], [lt31(2), lt32(1)], [lt31(3), lt32(3)]]), tx.vec], l);
        }
      }
    }
    l;
  }

  ---- (d.a)*(bxc) + (d.b)*(cxa) + (d.c)*(axb) = (abc)*d ----

  local rule11(yy:List Term):List Term ==
  {
    #yy<3 => yy;
    ~realVector?(per yy) => yy;
    xx := copy yy;
    xx := sort!(xx, termOrder?);
    l:List Term := empty;
    lr:List Term := xx;
    for tx in xx repeat
    {
      #tx.vec=1 =>
      {
        l := cons(tx, l);
        lr := rest lr;
      }
      break;
    }
    n := #lr;
    n<3 => l := append(l, lr);
    tt:Boolean := false;
    ttp:List Term := empty;
    ttp0:List Term := empty;
    while n>2 repeat
    {
      for i in 1..(n-2) repeat
      {
        for j in (i+1)..(n-1) repeat
        {
          for k in (j+1)..n repeat
          {
            if cond11? (lr(i), lr(j), lr(k)) then
            {
              ttp := [lr(i), lr(j), lr(k)];
              ttp0 := append([lr(s) for s in 1..(i-1)], [lr(s) for s in (i+1)..(j-1)]);
              ttp0 := append(ttp0, [lr(s) for s in (j+1)..(k-1)]);
              ttp0 := append(ttp0, [lr(s) for s in (k+1)..n]);
              lr := ttp0;
              tt := true;
              break;
            }
          }
          if tt then break;
        }
        if tt then break;
      }
      empty? ttp => break;
      l := append(l, comb11(ttp(1), ttp(2), ttp(3)));
      ttp := empty;
      n := #lr;
    }
    if ~empty? lr then l := append(l, lr);
    l;
  }

  ---- (d.h)(abc) = (d.a)(hbc) + (d.b)(ahc) + (d.c)(abh) ----

  local rule13(yy:List Term):List Term ==
  {
    xx := copy yy;
    #xx<3 => xx;
    xx := sort!(xx, termOrder?);
    l:List Term := empty;
    for tx in xx repeat
    {
      tp0 := tx.sca;
      n := #tp0;
      if n<2 then l := cons(tx, l);
      else
      {
        lt2:List String := empty;
        lt3:List String := empty;
        for i in 1..n-1 repeat
        {
          #tp0(i)=2 and #tp0(i+1)=3 =>
          {
            lt2 := tp0(i); lt3 := tp0(i+1);
            rt := append([tp0(j) for j in 1..(i-1)], [tp0(j) for j in (i+2)..n]);
            break;
          }
        }
        if empty? lt2 then l := cons(tx, l);
        else
        {
          l := cons([tx.coe, append(rt, [[lt2(1), lt3(1)], [lt2(2), lt3(2), lt3(3)]]), tx.vec], l);
          l := cons([tx.coe, append(rt, [[lt2(1), lt3(2)], [lt3(1), lt2(2), lt3(3)]]), tx.vec], l);
          l := cons([tx.coe, append(rt, [[lt2(1), lt3(3)], [lt3(1), lt3(2), lt2(2)]]), tx.vec], l);
        }
      }
    }
    l;
  }

}
