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
lemma LessEquivalentToNat(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
  match y {
    case Zero =>
      calc {
        Less(x, Zero);
        false;
      }
      assert UnaryToNat(y) == 0;
      assert !(UnaryToNat(x) < 0);
      assert Less(x, y) == false;
      assert (UnaryToNat(x) < UnaryToNat(y)) == false;
    case Suc(y_pred) =>
      if x.Suc? {
        LessEquivalentToNat(x.pred, y.pred);
        calc {
          Less(x, Suc(y_pred));
          Less(x.pred, y_pred); // by definition of Less
        }
        assert Less(x,y) <==> Less(x.pred, y_pred);
        assert Less(x,y) <==> UnaryToNat(x.pred) < UnaryToNat(y_pred); // by LessEquivalentToNat(x.pred, y.pred)
        assert Less(x,y) <==> UnaryToNat(x)-1 < UnaryToNat(y)-1;
        assert Less(x,y) <==> UnaryToNat(x) < UnaryToNat(y);
      } else { // x == Zero
        calc {
          Less(Zero, Suc(y_pred));
          true; // by definition, Less(Zero, Suc(y_pred)) is true if Suc(y_pred) != Zero
        }
        assert UnaryToNat(Zero) == 0;
        assert UnaryToNat(Suc(y_pred)) > 0;
        assert Less(Zero, Suc(y_pred)) == true;
        assert (UnaryToNat(Zero) < UnaryToNat(Suc(y_pred))) == true;
      }
  }
}

lemma AddCommutative(x: Unary, y: Unary)
  ensures Add(x, y) == Add(y, x)
  decreases UnaryToNat(y)
{
  if y.Zero? {
    assert Add(x, Zero) == x;
    assert Add(Zero, x) == x;
    assert Add(x, Zero) == Add(Zero, x); // This assertion is already implied by the above two statements, just to be explicit
  } else {
    AddCommutative(x, y.pred);
    calc {
      Add(x,y);
      Suc(Add(x, y.pred));
      Suc(Add(y.pred, x)); // by AddCommutative(x, y.pred)
      Add(y,x);
    }
  }
}

lemma AddAssociative(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
  decreases UnaryToNat(z)
{
  if z.Zero? {
    assert Add(Add(x,y), Zero) == Add(x,y);
    assert Add(x, Add(y, Zero)) == Add(x,y);
  } else {
    AddAssociative(x, y, z.pred);
    calc {
      Add(Add(x,y), Suc(z.pred));
      Suc(Add(Add(x,y), z.pred)); // by Add
      Suc(Add(x, Add(y,z.pred))); // by AddAssociative(x,y,z.pred)
      Add(x, Suc(Add(y,z.pred))); // by Add
      Add(x, Add(y, Suc(z.pred))); // by Add
    }
  }
}

lemma MulDistributesToAdd(x: Unary, y: Unary, z: Unary)
  ensures Add(Mul(x, y), Mul(x, z)) == Mul(x, Add(y, z))
  decreases UnaryToNat(x)
{
  if x.Zero? {
    assert Add(Mul(Zero, y), Mul(Zero, z)) == Add(Zero, Zero) == Zero;
    assert Mul(Zero, Add(y, z)) == Zero;
  } else {
    MulDistributesToAdd(x.pred, y, z);
    calc {
      Add(Mul(x, y), Mul(x, z));
      Add(Add(Mul(x.pred, y), y), Add(Mul(x.pred, z), z));
      Add(Add(Mul(x.pred, y), Mul(x.pred, z)), Add(y, z));
      {
        AddAssociative(Mul(x.pred, y), y, Mul(x.pred, z));
        AddCommutative(y, Mul(x.pred, z));
        AddAssociative(Mul(x.pred, y), Mul(x.pred, z), y);
      }
      Add(Mul(x.pred, Add(y, z)), Add(y, z)); // by MulDistributesToAdd(x.pred, y, z)
      Mul(x, Add(y, z));
    }
  }
}

lemma MulZero(x: Unary)
  ensures Mul(x, Zero) == Zero
  decreases UnaryToNat(x)
{
  if x.Suc? {
    MulZero(x.pred);
  }
}

lemma MulIdentity(x: Unary)
  ensures Mul(x, Suc(Zero)) == x
  decreases UnaryToNat(x)
{
  if x.Suc? {
    MulIdentity(x.pred);
    assert Mul(x, Suc(Zero)) == Add(Mul(x.pred, Suc(Zero)), Suc(Zero));
    assert Add(Mul(x.pred, Suc(Zero)), Suc(Zero)) == Add(x.pred, Suc(Zero)); // by MulIdentity(x.pred)
    assert Add(x.pred, Suc(Zero)) == Suc(Add(x.pred, Zero));
    assert Suc(Add(x.pred, Zero)) == Suc(x.pred);
    assert Suc(x.pred) == x;
  }
}

lemma SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x,y)) == Add(Suc(x),y)
  decreases UnaryToNat(y)
{
  if y.Zero? {
    assert Suc(Add(x,Zero)) == Suc(x);
    assert Add(Suc(x),Zero) == Suc(x);
  } else {
    SucAdd(x, y.pred);
    calc {
      Suc(Add(x,y));
      Suc(Suc(Add(x,y.pred)));
      Suc(Add(Suc(x),y.pred)); // by SucAdd(x,y.pred)
      Add(Suc(x), Suc(y.pred));
      Add(Suc(x), y);
    }
  }
}

lemma SubCorrect(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x,y), y) == x
  decreases UnaryToNat(y)
{
  if y.Zero? {
    assert Sub(x, Zero) == x;
    assert Add(x, Zero) == x;
  } else {
    SubCorrect(x.pred, y.pred);
    assert Sub(x,y) == Sub(x.pred, y.pred);
    assert Add(Sub(x.pred,y.pred), y.pred) == x.pred;
    assert Add(Sub(x,y), y) == Add(Sub(x.pred, y.pred), Suc(y.pred));
    assert Add(Sub(x.pred, y.pred), Suc(y.pred)) == Suc(Add(Sub(x.pred, y.pred), y.pred));
    assert Suc(Add(Sub(x.pred, y.pred), y.pred)) == Suc(x.pred);
    assert Suc(x.pred) == x;
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
  var d_curr := Zero;
  var x_curr := x;

  while !Less(x_curr, y)
    invariant Add(Mul(d_curr, y), x_curr) == x
    decreases UnaryToNat(x_curr)
  {
    SubCorrect(x_curr, y);
    var new_x_curr := Sub(x_curr, y);
    var new_d_curr := Suc(d_curr);
    calc {
      Add(Mul(new_d_curr, y), new_x_curr);
      Add(Mul(Suc(d_curr), y), Sub(x_curr, y));
      Add(Add(Mul(d_curr, y), y), Sub(x_curr, y));
      Add(Mul(d_curr, y), Add(y, Sub(x_curr, y))); {
        AddAssociative(Mul(d_curr, y), y, Sub(x_curr,y));
      }
      Add(Mul(d_curr, y), Add(Sub(x_curr, y), y)); {
        AddCommutative(y, Sub(x_curr, y));
      }
      Add(Mul(d_curr, y), x_curr); {
        SubCorrect(x_curr, y);
      }
      x;
    }
    x_curr := new_x_curr;
    d_curr := new_d_curr;
  }

  d := d_curr;
  m := x_curr;

  assert Add(Mul(d, y), m) == x; // from loop invariant
  assert Less(m, y); // from loop termination condition
}
// </vc-code>

