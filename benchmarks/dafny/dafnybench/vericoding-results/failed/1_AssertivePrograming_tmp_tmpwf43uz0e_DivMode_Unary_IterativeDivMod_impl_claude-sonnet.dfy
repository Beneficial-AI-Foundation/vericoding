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
lemma LessIrreflexive(x: Unary)
  ensures !Less(x, x)
{
  match x
  case Zero => 
  case Suc(x') => LessIrreflexive(x');
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
  match z
  case Zero => 
  case Suc(z') =>
    match y
    case Zero => 
    case Suc(y') =>
      if x.Suc? {
        LessTransitive(x.pred, y', z');
      }
}

lemma SubPreservesLess(x: Unary, y: Unary, z: Unary)
  requires !Less(x, y) && Less(z, y)
  ensures !Less(Sub(x, z), y)
{
  match x
  case Zero =>
    match z
    case Zero =>
    case Suc(z') =>
      assert false;
  case Suc(x') =>
    match z
    case Zero => 
    case Suc(z') =>
      SubPreservesLess(x', y, z');
}

lemma AddSubCancel(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(y, Sub(x, y)) == x
{
  match y
  case Zero => 
  case Suc(y') =>
    assert x.Suc?;
    AddSubCancel(x.pred, y');
}

lemma MulDistributesOverAdd(x: Unary, y: Unary, z: Unary)
  ensures Mul(Add(x, y), z) == Add(Mul(x, z), Mul(y, z))
{
  match x
  case Zero => 
  case Suc(x') =>
    MulDistributesOverAdd(x', y, z);
    AddAssociative(Mul(x', z), Mul(y, z), z);
}

lemma AddAssociative(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
{
  match z
  case Zero => 
  case Suc(z') =>
    AddAssociative(x, y, z');
}

lemma AddCommutative(x: Unary, y: Unary)
  ensures Add(x, y) == Add(y, x)
{
  match y
  case Zero =>
    AddZeroRight(x);
  case Suc(y') =>
    AddCommutative(x, y');
    AddSuccRight(y', x);
}

lemma AddZeroRight(x: Unary)
  ensures Add(x, Zero) == x
{
}

lemma AddSuccRight(x: Unary, y: Unary)
  ensures Add(x, Suc(y)) == Suc(Add(x, y))
{
  match x
  case Zero => 
  case Suc(x') =>
    AddSuccRight(x', y);
}

lemma SubDecreasesFirst(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Less(Sub(x, y), x)
{
  match y
  case Zero =>
  case Suc(y') =>
    match x
    case Zero =>
    case Suc(x') =>
      if y' == Zero {
        LessSucc(x');
      } else {
        SubDecreasesFirst(x', y');
        LessSuccMono(Sub(x', y'), x');
      }
}

lemma LessSucc(x: Unary)
  ensures Less(x, Suc(x))
{
  match x
  case Zero =>
  case Suc(x') =>
    LessSucc(x');
}

lemma LessSuccMono(x: Unary, y: Unary)
  requires Less(x, y)
  ensures Less(x, Suc(y))
{
  match y
  case Zero =>
  case Suc(y') =>
    if x.Suc? {
      LessSuccMono(x.pred, y');
    }
}

lemma InvariantPreservation(d: Unary, m: Unary, y: Unary, x: Unary)
  requires Add(Mul(d, y), m) == x && !Less(m, y) && y != Zero
  ensures Add(Mul(Suc(d), y), Sub(m, y)) == x
{
  calc {
    Add(Mul(Suc(d), y), Sub(m, y));
    Add(Add(Mul(d, y), y), Sub(m, y));
    { AddAssociative(Mul(d, y), y, Sub(m, y)); }
    Add(Mul(d, y), Add(y, Sub(m, y)));
    { AddCommutative(y, Sub(m, y)); }
    Add(Mul(d, y), Add(Sub(m, y), y));
    { AddSubCancel(m, y); }
    Add(Mul(d, y), m);
    x;
  }
}

lemma NotLessImpliesTotalOrder(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures x.Suc? && !Less(x.pred, y.pred)
{
  match x
  case Zero =>
    match y
    case Zero =>
    case Suc(y') =>
      assert Less(Zero, Suc(y'));
      assert false;
  case Suc(x') =>
    match y
    case Zero =>
    case Suc(y') =>
      assert !Less(x.pred, y.pred);
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
    decreases m
  {
    assert !Less(m, y);
    assert y != Zero;
    
    NotLessImpliesTotalOrder(m, y);
    assert m.Suc?;
    assert !Less(m.pred, y.pred);
    
    SubDecreasesFirst(m, y);
    assert Less(Sub(m, y), m);
    
    InvariantPreservation(d, m, y, x);
    
    d := Suc(d);
    m := Sub(m, y);
  }
  
  assert Less(m, y);
}
// </vc-code>

