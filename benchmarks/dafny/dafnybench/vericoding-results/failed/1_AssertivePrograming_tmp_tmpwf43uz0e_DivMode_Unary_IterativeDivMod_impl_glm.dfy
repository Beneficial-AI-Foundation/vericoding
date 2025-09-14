// Noa Leron 207131871
// Tsuri Farhana 315016907


// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
datatype Unary = Zero | Suc(pred: Unary)

ghost function UnaryToNat(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNat(x')
}

ghost function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Suc(NatToUnary(n-1))
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

function Add(x: Unary, y: Unary): Unary {
  match y
  case Zero => x
  case Suc(y') => Suc(Add(x, y'))
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero => x
  case Suc(y') => Sub(x.pred, y')
}

function Mul(x: Unary, y: Unary): Unary {
  match x
  case Zero => Zero
  case Suc(x') => Add(Mul(x', y), y)
}

/*
Goal: implement correcly and clearly, using iterative code (no recursion), documenting the proof obligations
    as we've learned, with assertions and a lemma for each proof goal

- DO NOT modify the specification or any of the definitions given in this file
- Not all definitions above are relevant, some are simply included as examples
- Feel free to use existing non-ghost functions/predicates in your code, and existing lemmas (for the proof) in your annotations
- New functions/predicates may be added ONLY as ghost
- If it helps you in any way, a recursive implementation + proof can be found in the book and the downloadable source file
  [https://program-proofs.com/code.html example code in Dafny, source file 7-Unary.dfy]
*/

method IterativeDivMod'(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SubAddLemma(a: Unary, b: Unary)
  requires !Less(b, a)
  ensures Add(a, Sub(b, a)) == b
{
  if a == Zero {
    assert Sub(b, Zero) == b;
  } else {
    var ap := a.pred;
    var bp := b.pred;
    SubAddLemma(ap, bp);
    assert a == Suc(ap);
    assert b == Suc(bp);
    calc {
      Add(a, Sub(b, a));
    ==   // Verified using a == Suc(ap)
      Add(Suc(ap), Sub(b, a));
    == { Sub(b, a) == Sub(bp, ap) }
      Add(Suc(ap), Sub(bp, ap));
    == { definition of Add }
      Suc(Add(ap, Sub(bp, ap)));
    == { SubAddLemma(ap, bp) }
      Suc(bp);
    == { b == Suc(bp) }
      b;
    }
  }
}

lemma LemmaMaintainsInvariant(d: Unary, m: Unary, y: Unary)
  requires !Less(m, y) && y != Zero
  requires Add(Mul(d, y), m) == x
  ensures Add(Mul(Suc(d), y), Sub(m, y)) == x
{
  calc {
    Add(Mul(Suc(d), y), Sub(m, y));
    == {Mul definition}
    Add(Add(Mul(d, y), y), Sub(m, y));
    == {Add is associative}
    Add(Mul(d, y), Add(y, Sub(m, y)));
    == {SubAddLemma(y, m)}
    Add(Mul(d, y), m);
  }
}
// </vc-helpers>

// <vc-spec>
method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
// </vc-spec>
// <vc-code>
{
  d := Zero;
  m := x;
  while !Less(m, y)
    invariant Add(Mul(d, y), m) == x
    invariant !Less(m, y) ==> y != Zero
  {
    LemmaMaintainsInvariant(d, m, y);
    d := Suc(d);
    m := Sub(m, y);
  }
}
// </vc-code>

