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
lemma AddZero(x: Unary)
  ensures Add(x, Zero) == x
{
  // Follows directly from the definition of Add
}

lemma AddSuc(x: Unary, y: Unary)
  ensures Add(x, Suc(y)) == Suc(Add(x, y))
{
  // follows from definition
}

lemma MulZero(y: Unary)
  ensures Mul(Zero, y) == Zero
{
  // follows from definition
}

lemma MulSuc(x: Unary, y: Unary)
  ensures Mul(Suc(x), y) == Add(Mul(x, y), y)
{
  // follows from definition
}

lemma SubAdd(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
{
  match y {
    case Zero =>
      AddZero(x);
    case Suc(y') =>
      SubAdd(x.pred, y');
      AddSuc(Sub(x.pred, y'), y');
  }
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
  match z {
    case Zero =>
    case Suc(z') =>
      if y == Zero {
      } else {
        match y {
          case Suc(y') =>
            if x == Zero {
            } else {
              match x {
                case Suc(x') =>
                  LessTransitive(x', y', z');
              }
            }
        }
      }
  }
}

lemma AddAssoc(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
{
  match z {
    case Zero =>
      AddZero(y);
      AddZero(Add(x, y));
    case Suc(z') =>
      AddAssoc(x, y, z');
  }
}

lemma LessPred(x: Unary)
  requires x.Suc?
  ensures Less(x.pred, x)
{
  match x {
    case Suc(x') =>
      // Need to show Less(x', Suc(x'))
      // By definition, this means Suc(x') != Zero (true) && (x'.Suc? ==> Less(x'.pred, x'))
      if x' == Zero {
        // Less(Zero, Suc(Zero)) holds by definition
      } else {
        LessPred(x');
      }
  }
}

lemma SubLess(x: Unary, y: Unary)
  requires y != Zero && !Less(x, y)
  ensures Less(Sub(x, y), x)
{
  match y {
    case Suc(y') =>
      if y' == Zero {
        assert x.Suc?;  // Since !Less(x, Suc(Zero)), x must be Suc
        assert Sub(x, y) == x.pred;
        LessPred(x);
      } else {
        assert x.Suc?;  // Since !Less(x, Suc(y')) with y' != Zero
        SubLess(x.pred, y');
        // Sub(x.pred, y') < x.pred < x
        assert Less(Sub(x.pred, y'), x.pred);
        LessPred(x);
        assert Less(x.pred, x);
        LessTransitive(Sub(x.pred, y'), x.pred, x);
      }
  }
}

lemma AddCommutes(x: Unary, y: Unary)
  ensures Add(x, y) == Add(y, x)
{
  match y {
    case Zero =>
      AddZero(x);
    case Suc(y') =>
      AddCommutes(x, y');
      calc {
        Add(x, Suc(y'));
        == Suc(Add(x, y'));
        == Suc(Add(y', x));
        == Add(Suc(y'), x);
      }
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
  
  // Establish loop invariant on entry
  assert Mul(Zero, y) == Zero by { MulZero(y); }
  assert Add(Zero, x) == x by { AddCommutes(Zero, x); }
  assert Add(Mul(d, y), m) == x;
  
  while !Less(m, y)
    invariant Add(Mul(d, y), m) == x
    decreases m
  {
    var oldM := m;
    var oldD := d;
    
    // Prove that m will decrease
    assert !Less(oldM, y);  // From loop condition
    SubLess(oldM, y);
    assert Less(Sub(oldM, y), oldM);
    
    // Update values
    m := Sub(oldM, y);
    d := Suc(oldD);
    
    // The decreases is now verified since m < oldM
    assert Less(m, oldM);
    
    // Prove invariant preservation
    assert Add(Sub(oldM, y), y) == oldM by { SubAdd(oldM, y); }
    assert Mul(Suc(oldD), y) == Add(Mul(oldD, y), y) by { MulSuc(oldD, y); }
    
    calc {
      Add(Mul(d, y), m);
      == Add(Mul(Suc(oldD), y), m);
      == Add(Add(Mul(oldD, y), y), m);
      == { AddAssoc(Mul(oldD, y), y, m); }
      Add(Mul(oldD, y), Add(y, m));
      == Add(Mul(oldD, y), Add(y, Sub(oldM, y)));
      == { AddCommutes(y, Sub(oldM, y)); }
      Add(Mul(oldD, y), Add(Sub(oldM, y), y));
      == Add(Mul(oldD, y), oldM);
      == x;
    }
  }
}
// </vc-code>

