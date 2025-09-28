// <vc-preamble>
// IEEE 754-like floating point representation
datatype IEEEFloat = 
  | Finite(value: real)
  | PositiveInfinity
  | NegativeInfinity
  | NaN

// Predicate to check if a float is finite
ghost predicate IsFinite(f: IEEEFloat) {
  f.Finite?
}

// Predicate to check if a float is positive
ghost predicate IsPositive(f: IEEEFloat) {
  match f {
    case Finite(v) => v > 0.0
    case PositiveInfinity => true
    case _ => false
  }
}

// Predicate to check if a float is negative
ghost predicate IsNegative(f: IEEEFloat) {
  match f {
    case Finite(v) => v < 0.0
    case NegativeInfinity => true
    case _ => false
  }
}

// Float addition
function FloatAdd(a: IEEEFloat, b: IEEEFloat): IEEEFloat {
  match (a, b) {
    case (NegativeInfinity, Finite(_)) => NegativeInfinity
    case (Finite(_), NegativeInfinity) => NegativeInfinity
    case (Finite(x), Finite(y)) => Finite(x + y)
    case (PositiveInfinity, PositiveInfinity) => PositiveInfinity
    case (NegativeInfinity, NegativeInfinity) => NegativeInfinity
    case _ => NaN
  }
}

// Float multiplication
function FloatMult(a: IEEEFloat, b: IEEEFloat): IEEEFloat {
  match (a, b) {
    case (NegativeInfinity, Finite(x)) => if x > 0.0 then NegativeInfinity else if x < 0.0 then PositiveInfinity else NaN
    case (Finite(x), NegativeInfinity) => if x > 0.0 then NegativeInfinity else if x < 0.0 then PositiveInfinity else NaN
    case (NegativeInfinity, NegativeInfinity) => PositiveInfinity
    case (Finite(x), Finite(y)) => Finite(x * y)
    case _ => NaN
  }
}

// Float division
function FloatDiv(a: IEEEFloat, b: IEEEFloat): IEEEFloat {
  match (a, b) {
    case (NegativeInfinity, Finite(x)) => if x > 0.0 then NegativeInfinity else if x < 0.0 then PositiveInfinity else NaN
    case (Finite(x), Finite(y)) => if y != 0.0 then Finite(x / y) else NaN
    case _ => NaN
  }
}

// Float absolute value
function FloatAbs(f: IEEEFloat): IEEEFloat {
  match f {
    case Finite(v) => Finite(if v >= 0.0 then v else -v)
    case NegativeInfinity => PositiveInfinity
    case PositiveInfinity => PositiveInfinity
    case NaN => NaN
  }
}

// Float less than comparison
predicate FloatLess(a: IEEEFloat, b: IEEEFloat) {
  match (a, b) {
    case (NegativeInfinity, Finite(_)) => true
    case (NegativeInfinity, PositiveInfinity) => true
    case (Finite(x), Finite(y)) => x < y
    case (Finite(_), PositiveInfinity) => true
    case _ => false
  }
}

// Float negation
function FloatNegate(f: IEEEFloat): IEEEFloat {
  match f {
    case Finite(v) => Finite(-v)
    case PositiveInfinity => NegativeInfinity
    case NegativeInfinity => PositiveInfinity
    case NaN => NaN
  }
}

// Method that returns negative infinity with all required properties
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NINF() returns (result: IEEEFloat)
  ensures result == NegativeInfinity
  // Property 1: NINF is less than all finite values
  ensures forall x :: IsFinite(x) ==> FloatLess(result, x)
  // Property 2: NINF + finite = NINF  
  ensures forall x :: IsFinite(x) ==> FloatAdd(result, x) == result
  // Property 3: NINF * positive finite = NINF
  ensures forall x :: IsFinite(x) && IsPositive(x) ==> FloatMult(result, x) == result
  // Property 4: NINF * negative finite = positive infinity
  ensures forall x :: IsFinite(x) && IsNegative(x) ==> FloatMult(result, x) == FloatNegate(result)
  // Property 5: NINF / finite non-zero = NINF (with appropriate sign)
  ensures forall x :: IsFinite(x) && x != Finite(0.0) ==>
    (IsPositive(x) ==> FloatDiv(result, x) == result) &&
    (IsNegative(x) ==> FloatDiv(result, x) == FloatNegate(result))
  // Property 6: NINF is not finite
  ensures !IsFinite(result)
  // Property 7: NINF is negative
  ensures IsNegative(result)
  // Property 8: NINF squared is positive infinity
  ensures FloatMult(result, result) == FloatNegate(result)
  // Property 9: Absolute value of NINF is positive infinity
  ensures FloatAbs(result) == FloatNegate(result)
// </vc-spec>
// <vc-code>
{
  result := NegativeInfinity;
}
// </vc-code>
