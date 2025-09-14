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
lemma AddAssoc(a: Unary, b: Unary, c: Unary)
  ensures Add(Add(a, b), c) == Add(a, Add(b, c))
  decreases c
{
  match c
  case Zero => {}
  case Suc(c') =>
    AddAssoc(a, b, c');
    assert Add(Add(a, b), Suc(c')) == Suc(Add(Add(a, b), c'));
    assert Add(a, Add(b, Suc(c'))) == Suc(Add(a, Add(b, c')));
    assert Add(Add(a, b), Suc(c')) == Add(a, Add(b, Suc(c')));
}

lemma AddY_Sub(m: Unary, y: Unary)
  requires !Less(m, y)
  requires y != Zero
  ensures Add(y, Sub(m, y)) == m
  decreases y
{
  match y
  case Zero =>
    // impossible due to requires y != Zero
    assert false;
  case Suc(y') =>
    match m
    case Zero =>
      // impossible because !Less(Zero, Suc(_)) cannot hold
      assert false;
    case Suc(pm) =>
      // Sub(Suc(pm), Suc(y')) == Sub(pm, y')
      AddY_Sub(pm, y');
      assert Add(y, Sub(m, y)) == Suc(Add(y', Sub(pm, y')));
      assert m == Suc(pm);
      assert Add(y', Sub(pm, y')) == pm;
      assert Suc(Add(y', Sub(pm, y'))) == Suc(pm);
}

lemma Mul_Suc_eq(d: Unary, y: Unary)
  ensures Mul(Suc(d), y) == Add(Mul(d, y), y)
  decreases d
{
  match d
  case Zero => {}
  case Suc(d') =>
    Mul_Suc_eq(d', y);
}

lemma UnaryToNat_Sub(m: Unary, y: Unary)
  requires !Less(m, y)
  ensures UnaryToNat(Sub(m, y)) == UnaryToNat(m) - UnaryToNat(y)
  decreases y
{
  match y
  case Zero =>
    // Sub(m, Zero) == m
    assert Sub(m, Zero) == m;
    assert UnaryToNat(Sub(m, Zero)) == UnaryToNat(m);
    assert UnaryToNat(y) == 0;
    assert UnaryToNat(m) - UnaryToNat(y) == UnaryToNat(m);
  case Suc(y') =>
    match m
    case Zero =>
      // impossible because !Less(Zero, Suc(_)) cannot hold
      assert false;
    case Suc(pm) =>
      // Sub(Suc(pm), Suc(y')) == Sub(pm, y')
      UnaryToNat_Sub(pm, y');
      assert UnaryToNat(Sub(Suc(pm), Suc(y'))) == UnaryToNat(Sub(pm, y'));
      assert UnaryToNat(Sub(pm, y')) == UnaryToNat(pm) - UnaryToNat(y');
      assert UnaryToNat(Suc(pm)) == 1 + UnaryToNat(pm);
      assert UnaryToNat(Suc(y')) == 1 + UnaryToNat(y');
      // arithmetic: (1 + a) - (1 + b) == a - b for nats
      assert UnaryToNat(pm) - UnaryToNat(y') == UnaryToNat(Suc(pm)) - UnaryToNat(Suc(y'));
      assert UnaryToNat(Sub(Suc(pm), Suc(y'))) == UnaryToNat(Suc(pm)) - UnaryToNat(Suc(y'));
}
// </vc-helpers>

// <vc-spec>
method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
// </vc-spec>
// <vc-code>
{
  // classical iterative division by repeated subtraction
  d := Zero;
  m := x;

  // establish invariant initially
  assert Add(Mul(d, y), m) == x;

  while !Less(m, y)
    invariant Add(Mul(d, y), m) == x
    decreases UnaryToNat(m)
  {
    // Sub(m, y) is defined because loop guard ensures !Less(m,y)
    UnaryToNat_Sub(m, y);
    assert UnaryToNat(Sub(m, y)) == UnaryToNat(m) - UnaryToNat(y);
    // y != Zero (precondition), so UnaryToNat(y) >= 1
    match y
    case Zero =>
      assert false;
    case Suc(_) =>
      assert UnaryToNat(y) >= 1;
    assert UnaryToNat(Sub(m, y)) < UnaryToNat(m);

    // prepare proof that invariant is preserved after:
    // Add(Mul(Suc(d), y), Sub(m, y)) == x
    Mul_Suc_eq(d, y);
    AddAssoc(Mul(d, y), y, Sub(m, y));
    // from !Less(m,y) and precondition y != Zero
    AddY_Sub(m, y);
    // combine lemmas to conclude preservation
    assert Add(Mul(Suc(d), y), Sub(m, y)) == Add(Mul(d, y), m);

    m := Sub(m, y);
    d := Suc(d);
  }

  // final facts follow from the invariant and loop exit condition
  assert Add(Mul(d, y), m) == x;
  assert Less(m, y);
}
// </vc-code>

