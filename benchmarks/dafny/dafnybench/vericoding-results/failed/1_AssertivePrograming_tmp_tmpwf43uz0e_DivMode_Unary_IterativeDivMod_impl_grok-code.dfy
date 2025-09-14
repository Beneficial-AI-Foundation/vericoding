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
lemma UnaryToNat_Add(x: Unary, y: Unary)
  ensures UnaryToNat(Add(x, y)) == UnaryToNat(x) + UnaryToNat(y)
{
  match y
  case Zero =>
  case Suc(y') =>
    UnaryToNat_Add(x, y');
    calc == {
      UnaryToNat(Add(x, Suc(y')));
      == 1 + UnaryToNat(Add(x, y'));
      == 1 + UnaryToNat(x) + UnaryToNat(y');
      == UnaryToNat(x) + UnaryToNat(Suc(y'));
    }
}

lemma UnaryToNat_Sub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures UnaryToNat(Sub(x, y)) == UnaryToNat(x) - UnaryToNat(y)
{
  match y {
    case Zero => {
      assert Sub(x, Zero) == x;
    }
    case Suc(y') => {
      UnaryToNat_Sub(x.pred, y');
    }
  }
}

lemma UnaryToNat_Mul(x: Unary, y: Unary)
  ensures UnaryToNat(Mul(x, y)) == UnaryToNat(x) * UnaryToNat(y)
{
  match x
  case Zero =>
  case Suc(x') =>
    UnaryToNat_Mul(x', y);
    calc == {
      UnaryToNat(Mul(Suc(x'), y));
      == UnaryToNat(Add(Mul(x', y), y));
      { UnaryToNat_Add(Mul(x', y), y); }
      UnaryToNat(Mul(x', y)) + UnaryToNat(y);
      == UnaryToNat(x') * UnaryToNat(y) + UnaryToNat(y);
      == (UnaryToNat(x') + 1) * UnaryToNat(y);
      == UnaryToNat(Suc(x')) * UnaryToNat(y);
    }
}

lemma Sub_add_cancel(y: Unary, r: Unary)
  requires !Less(r, y)
  ensures Add(y, Sub(r, y)) == r
{
  if r == Zero {
    assert Sub(Zero, y) == Zero;
    assert Add(y, Zero) == y;
  } else {
    match y
    case Zero =>
    case Suc(y') =>
      Sub_add_cancel(y', r.pred);
      calc == {
        Sub(Suc(r.pred), Suc(y'));
        == Suc(Sub(r.pred, y'));
        Add(Suc(y'), Suc(Sub(r.pred, y')));
        == Suc(Add(y', Sub(r.pred, y')));
        == Suc(r.pred);
      }
  }
}

lemma UniqueUnary(n: nat, a: Unary, b: Unary)
  requires UnaryToNat(a) == n && UnaryToNat(b) == n
  ensures a == b
{
  if n == 0 {
    assert a == b;
  } else {
    match a
    case Zero => assert false;
    match b
    case Zero => assert false;
    case Suc(a') =>
      calc == {
        UnaryToNat(Suc(a')) == n;
        == UnaryToNat(Suc(b.pred));
        == 1 + UnaryToNat(b.pred);
        == UnaryToNat(b);
      }
      UniqueUnary(n-1, a', b.pred);
  }
}

lemma AddMulSub(d: Unary, r: Unary, y: Unary)
  requires !Less(r, y)
  ensures UnaryToNat(Add(Mul(Add(d, Suc(Zero)), y), Sub(r, y))) == UnaryToNat(Add(Mul(d, y), r))
{
  UnaryToNat_Add(Mul(d, y), r);
  UnaryToNat_Add(Mul(Add(d, Suc(Zero)), y), Sub(r, y));
  UnaryToNat_Sub(r, y);
  // Use existing lemmas
  var ds := Add(d, Suc(Zero));
  UnaryToNat_Add(d, Suc(Zero));
  UnaryToNat_Mul(ds, y);
  calc == {
    UnaryToNat(ds);
    == UnaryToNat(d) + 1;
  }
  calc == {
    UnaryToNat(Mul(ds, y));
    UnaryToNat_Mul(ds, y);
    == UnaryToNat(ds) * UnaryToNat(y);
    == (UnaryToNat(d) + 1) * UnaryToNat(y);
  }
  calc == {
    UnaryToNat(Add(Mul(ds, y), Sub(r, y)));
    { UnaryToNat_Add(Mul(ds, y), Sub(r, y)); }
    UnaryToNat(Mul(ds, y)) + UnaryToNat(Sub(r, y));
    { UnaryToNat_Sub(r, y); }
    UnaryToNat(Mul(ds, y)) + (UnaryToNat(r) - UnaryToNat(y));
    == (UnaryToNat(d) + 1) * UnaryToNat(y) + (UnaryToNat(r) - UnaryToNat(y));
    == UnaryToNat(d) * UnaryToNat(y) + UnaryToNat(y) + UnaryToNat(r) - UnaryToNat(y);
    == UnaryToNat(Mul(d, y)) + UnaryToNat(r);
    { UnaryToNat_Add(Mul(d, y), r); }
    UnaryToNat(Add(Mul(d, y), r));
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
  var r := x;
  while !Less(r, y)
    invariant Add(Mul(d, y), r) == x
    decreases UnaryToNat(r)
  {
    AddMulSub(d, r, y);
    r := Sub(r, y);
    d := Add(d, Suc(Zero));
    UniqueUnary(UnaryToNat(x), Add(Mul(d, y), r), x);
  }
  m := r;
}
// </vc-code>

