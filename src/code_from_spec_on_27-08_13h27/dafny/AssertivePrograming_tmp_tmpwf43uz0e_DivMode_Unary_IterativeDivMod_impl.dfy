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
ghost function UnaryToNatAux(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNatAux(x')
}

lemma AddCorrect(x: Unary, y: Unary)
  ensures UnaryToNatAux(Add(x, y)) == UnaryToNatAux(x) + UnaryToNatAux(y)
{
  match y {
    case Zero => {}
    case Suc(y') => {
      calc {
        UnaryToNatAux(Add(x, y));
        UnaryToNatAux(Suc(Add(x, y')));
        1 + UnaryToNatAux(Add(x, y'));
        { AddCorrect(x, y'); }
        1 + (UnaryToNatAux(x) + UnaryToNatAux(y'));
        UnaryToNatAux(x) + (1 + UnaryToNatAux(y'));
        UnaryToNatAux(x) + UnaryToNatAux(y);
      }
    }
  }
}

lemma MulCorrect(x: Unary, y: Unary)
  ensures UnaryToNatAux(Mul(x, y)) == UnaryToNatAux(x) * UnaryToNatAux(y)
{
  match x {
    case Zero => {}
    case Suc(x') => {
      calc {
        UnaryToNatAux(Mul(x, y));
        UnaryToNatAux(Add(Mul(x', y), y));
        { AddCorrect(Mul(x', y), y); }
        UnaryToNatAux(Mul(x', y)) + UnaryToNatAux(y);
        { MulCorrect(x', y); }
        (UnaryToNatAux(x') * UnaryToNatAux(y)) + UnaryToNatAux(y);
        (UnaryToNatAux(x) - 1) * UnaryToNatAux(y) + UnaryToNatAux(y);
        UnaryToNatAux(x) * UnaryToNatAux(y);
      }
    }
  }
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) ==> UnaryToNatAux(x) < UnaryToNatAux(y)
{
  if Less(x, y) {
    match y {
      case Suc(y') => {
        if x.Suc? {
          LessCorrect(x.pred, y.pred);
        }
      }
      case Zero => {}
    }
  }
}

lemma SubCorrect(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures UnaryToNatAux(Sub(x, y)) == UnaryToNatAux(x) - UnaryToNatAux(y)
{
  match y {
    case Zero => {}
    case Suc(y') => {
      calc {
        UnaryToNatAux(Sub(x, y));
        UnaryToNatAux(Sub(x.pred, y'));
        { SubCorrect(x.pred, y'); }
        UnaryToNatAux(x.pred) - UnaryToNatAux(y');
        (UnaryToNatAux(x) - 1) - (UnaryToNatAux(y) - 1);
        UnaryToNatAux(x) - UnaryToNatAux(y);
      }
    }
  }
}

lemma AddAssociative(x: Unary, y: Unary, z: Unary)
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
{
  match z {
    case Zero => {}
    case Suc(z') => {
      calc {
        Add(Add(x, y), z);
        Suc(Add(Add(x, y), z'));
        { AddAssociative(x, y, z'); }
        Suc(Add(x, Add(y, z')));
        Add(x, Add(y, z));
      }
    }
  }
}

lemma SubAddCorrect(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(y, Sub(x, y)) == x
{
  calc {
    UnaryToNatAux(Add(y, Sub(x, y)));
    { AddCorrect(y, Sub(x, y)); }
    UnaryToNatAux(y) + UnaryToNatAux(Sub(x, y));
    { SubCorrect(x, y); }
    UnaryToNatAux(y) + (UnaryToNatAux(x) - UnaryToNatAux(y));
    UnaryToNatAux(x);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var quotient := Zero;
  var remainder := x;
  
  while !Less(remainder, y)
    decreases UnaryToNatAux(remainder)
    invariant Add(Mul(quotient, y), remainder) == x
    invariant Less(remainder, y) ==> remainder == Zero
  {
    var newRemainder := Sub(remainder, y);
    calc {
      Add(Mul(Suc(quotient), y), newRemainder);
      Add(Add(Mul(quotient, y), y), Sub(remainder, y));
      { AddAssociative(Mul(quotient, y), y, Sub(remainder, y)); }
      Add(Mul(quotient, y), Add(y, Sub(remainder, y)));
      { SubAddCorrect(remainder, y); }
      Add(Mul(quotient, y), remainder);
      x;
    }
    remainder := newRemainder;
    quotient := Suc(quotient);
    calc {
      UnaryToNatAux(newRemainder);
      { SubCorrect(remainder, y); }
      UnaryToNatAux(remainder) - UnaryToNatAux(y);
      < UnaryToNatAux(remainder);
    }
  }
  
  return quotient, remainder;
}
// </vc-code>
