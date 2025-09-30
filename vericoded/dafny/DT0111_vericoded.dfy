// <vc-preamble>
// IEEE 754 float representation including NaN
datatype Float = Finite(value: real) | PosInf | NegInf | NaN

// Predicate to check if a float represents a finite value
predicate IsFinite(x: Float) {
    x.Finite?
}

// Predicate to check if a float is positive
predicate IsPositive(x: Float) {
    match x {
        case Finite(v) => v > 0.0
        case PosInf => true
        case NegInf => false
        case NaN => false
    }
}

// Predicate to check if a float is negative  
predicate IsNegative(x: Float) {
    match x {
        case Finite(v) => v < 0.0
        case PosInf => false
        case NegInf => true
        case NaN => false
    }
}

// Addition operation for IEEE 754 floats
function FloatAdd(x: Float, y: Float): Float {
    match (x, y) {
        case (Finite(a), Finite(b)) => Finite(a + b)
        case (PosInf, Finite(_)) => PosInf
        case (Finite(_), PosInf) => PosInf
        case (NegInf, Finite(_)) => NegInf
        case (Finite(_), NegInf) => NegInf
        case (PosInf, PosInf) => PosInf
        case (NegInf, NegInf) => NegInf
        case (PosInf, NegInf) => NaN
        case (NegInf, PosInf) => NaN
        case (NaN, _) => NaN
        case (_, NaN) => NaN
    }
}

// Multiplication operation for IEEE 754 floats
function FloatMul(x: Float, y: Float): Float {
    match (x, y) {
        case (Finite(a), Finite(b)) => Finite(a * b)
        case (PosInf, Finite(b)) => if b > 0.0 then PosInf else if b < 0.0 then NegInf else NaN
        case (Finite(a), PosInf) => if a > 0.0 then PosInf else if a < 0.0 then NegInf else NaN
        case (NegInf, Finite(b)) => if b > 0.0 then NegInf else if b < 0.0 then PosInf else NaN
        case (Finite(a), NegInf) => if a > 0.0 then NegInf else if a < 0.0 then PosInf else NaN
        case (PosInf, PosInf) => PosInf
        case (PosInf, NegInf) => NegInf
        case (NegInf, PosInf) => NegInf
        case (NegInf, NegInf) => PosInf
        case (NaN, _) => NaN
        case (_, NaN) => NaN
    }
}

// Division operation for IEEE 754 floats
function FloatDiv(x: Float, y: Float): Float {
    match (x, y) {
        case (Finite(a), Finite(b)) => if b != 0.0 then Finite(a / b) else if a > 0.0 then PosInf else if a < 0.0 then NegInf else NaN
        case (PosInf, Finite(b)) => if b > 0.0 then PosInf else if b < 0.0 then NegInf else NaN
        case (NegInf, Finite(b)) => if b > 0.0 then NegInf else if b < 0.0 then PosInf else NaN
        case (Finite(_), PosInf) => Finite(0.0)
        case (Finite(_), NegInf) => Finite(0.0)
        case (PosInf, PosInf) => NaN
        case (PosInf, NegInf) => NaN
        case (NegInf, PosInf) => NaN
        case (NegInf, NegInf) => NaN
        case (NaN, _) => NaN
        case (_, NaN) => NaN
    }
}

// Negation operation for IEEE 754 floats
function FloatNeg(x: Float): Float {
    match x {
        case Finite(v) => Finite(-v)
        case PosInf => NegInf
        case NegInf => PosInf
        case NaN => NaN
    }
}

// Comparison for IEEE 754 floats
predicate FloatGreater(x: Float, y: Float) {
    match (x, y) {
        case (Finite(a), Finite(b)) => a > b
        case (PosInf, _) => y != PosInf && y != NaN
        case (_, NegInf) => x != NegInf && x != NaN
        case (Finite(_), PosInf) => false
        case (NegInf, _) => false
        case (NaN, _) => false
        case (_, NaN) => false
    }
}

// IEEE 754 positive infinity constant
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method inf() returns (result: Float)
    // Property 1: inf is greater than all finite values
    ensures forall x: Float :: IsFinite(x) ==> FloatGreater(result, x)
    // Property 2: inf + finite = inf  
    ensures forall x: Float :: IsFinite(x) ==> FloatAdd(result, x) == result
    // Property 3: inf * positive finite = inf
    ensures forall x: Float :: IsFinite(x) && IsPositive(x) ==> FloatMul(result, x) == result
    // Property 4: inf * negative finite = -inf
    ensures forall x: Float :: IsFinite(x) && IsNegative(x) ==> FloatMul(result, x) == FloatNeg(result)
    // Property 5: inf / finite non-zero = inf (with appropriate sign)
    ensures forall x: Float :: IsFinite(x) && x != Finite(0.0) ==> 
        (IsPositive(x) ==> FloatDiv(result, x) == result) &&
        (IsNegative(x) ==> FloatDiv(result, x) == FloatNeg(result))
    // Property 6: inf is not finite
    ensures !IsFinite(result)
    // Property 7: inf is positive
    ensures IsPositive(result)
    // Property 8: result is specifically positive infinity
    ensures result == PosInf
// </vc-spec>
// <vc-code>
{
  result := PosInf;
}
// </vc-code>
