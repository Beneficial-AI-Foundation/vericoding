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
lemma lemma_UnaryToNatZero() ensures UnaryToNat(Zero) == 0 {}
lemma lemma_UnaryToNatSuc(x: Unary) ensures UnaryToNat(Suc(x)) == 1 + UnaryToNat(x) {}

lemma lemma_LessZero(x: Unary)
  ensures Less(x, Zero) == false
{}
  
lemma lemma_LessSuc(x: Unary, y: Unary)
  ensures Less(Suc(x), Suc(y)) == Less(x, y)
{}
  
lemma lemma_AddZero(x: Unary)
  ensures Add(x, Zero) == x
{}
  
lemma lemma_AddSuc(x: Unary, y: Unary)
  ensures Add(x, Suc(y)) == Suc(Add(x, y))
{}

lemma lemma_MulZero(y: Unary)
  ensures Mul(Zero, y) == Zero
{}
  
lemma lemma_MulSuc(x: Unary, y: Unary)
  ensures Mul(Suc(x), y) == Add(Mul(x, y), y)
{}

lemma lemma_SubZero(x: Unary)
  requires !Less(x, Zero)
  ensures Sub(x, Zero) == x
{}
  
lemma lemma_SubSuc(x: Unary, y: Unary)
  requires !Less(Suc(x), Suc(y))
  ensures Sub(Suc(x), Suc(y)) == Sub(x, y)
{}

lemma lemma_AddAssociative(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
{
  match z {
    case Zero => 
      assert Add(Add(x, y), Zero) == Add(x, y);
      assert Add(x, Add(y, Zero)) == Add(x, y);
    case Suc(z') =>
      calc == {
        Add(Add(x, y), Suc(z'));
        Suc(Add(Add(x, y), z'));
        { lemma_AddAssociative(x, y, z'); }
        Suc(Add(x, Add(y, z')));
        Add(x, Suc(Add(y, z')));
        Add(x, Add(y, Suc(z')));
      }
  }
}

lemma lemma_LessAdd(x: Unary, y: Unary)
  requires y != Zero
  ensures Less(x, Add(x, y))
{
  match y {
    case Zero => 
    case Suc(y') =>
      assert Less(x, Suc(Add(x, y')));
  }
}

lemma lemma_AddCancel(x: Unary, y: Unary, z: Unary)
  requires Add(x, y) == Add(x, z)
  ensures y == z
{
  match x {
    case Zero => 
      assert Add(Zero, y) == y;
      assert Add(Zero, z) == z;
    case Suc(x') =>
      calc == {
        Add(Suc(x'), y);
        Suc(Add(x', y));
        Suc(Add(x', z));
        Add(Suc(x'), z);
      };
  }
}

ghost function DecrementIfPositive(x: Unary): Unary
  requires x != Zero
  ensures DecrementIfPositive(x) == x.pred
{
  match x {
    case Suc(x') => x'
    case Zero => Zero
  }
}

lemma lemma_MulAddDistributive(d: Unary, y: Unary, m: Unary)
  ensures Add(Mul(Suc(d), y), m) == Add(Add(Mul(d, y), y), m)
{
  assert Mul(Suc(d), y) == Add(Mul(d, y), y) by lemma_MulSuc(d, y);
}

lemma lemma_SubPreservesInvariant(d: Unary, y: Unary, m: Unary)
  requires !Less(m, y) && m != Zero
  ensures Add(Mul(Suc(d), y), Sub(m, y)) == Add(Mul(d, y), m)
{
  lemma_MulSuc(d, y);
  assert Mul(Suc(d), y) == Add(Mul(d, y), y);
  calc == {
    Add(Mul(Suc(d), y), Sub(m, y));
    Add(Add(Mul(d, y), y), Sub(m, y));
    { lemma_AddAssociative(Mul(d, y), y, Sub(m, y)); }
    Add(Mul(d, y), Add(y, Sub(m, y)));
    { assert Add(y, Sub(m, y)) == m; }
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
  
  while (m != Zero && !Less(m, y))
    invariant Add(Mul(d, y), m) == x
    invariant !Less(m, y) || m == Zero
    decreases UnaryToNat(m)
  {
    lemma_SubPreservesInvariant(d, y, m);
    d := Suc(d);
    m := Sub(m, y);
  }
}
// </vc-code>

