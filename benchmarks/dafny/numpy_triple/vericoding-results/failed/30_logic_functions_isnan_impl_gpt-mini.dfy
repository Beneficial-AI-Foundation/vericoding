// <vc-preamble>
// Abstract floating point type that can represent NaN, finite values, and infinities
datatype FloatValue = Finite(value: real) | NaN | PosInf | NegInf

// Predicate to check if a FloatValue is NaN
ghost predicate IsNaN(x: FloatValue)
{
    x.NaN?
}

// Predicate to check if a FloatValue is finite
ghost predicate IsFinite(x: FloatValue)
{
    x.Finite?
}

// Predicate to check if a FloatValue is infinite
ghost predicate IsInfinite(x: FloatValue)
{
    x.PosInf? || x.NegInf?
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove complement property of IsNaN */
lemma IsNaN_Complement(x: FloatValue)
  ensures IsNaN(x) <==> !(IsFinite(x) || IsInfinite(x))
{
  match x
  case NaN =>
    assert IsNaN(x);
    assert !(IsFinite(x) || IsInfinite(x));
  case Finite(_) =>
    assert !IsNaN(x);
    assert IsFinite(x);
  case PosInf =>
    assert !IsNaN(x);
    assert IsInfinite(x);
  case NegInf =>
    assert !IsNaN(x);
    assert IsInfinite(x);
}

// </vc-helpers>

// <vc-spec>
method IsNan(x: seq<FloatValue>) returns (result: seq<bool>)
    ensures |result| == |x|
    // Core NaN detection property: result[i] is true iff x[i] is NaN
    ensures forall i :: 0 <= i < |x| ==> (result[i] <==> IsNaN(x[i]))
    // IEEE 754 fundamental NaN property: NaN ≠ NaN (self-inequality)
    ensures forall i :: 0 <= i < |x| ==> (result[i] ==> x[i] != x[i])
    // Non-NaN values produce false results
    ensures forall i :: 0 <= i < |x| ==> (!IsNaN(x[i]) ==> !result[i])
    // Finite values always produce false results
    ensures forall i :: 0 <= i < |x| ==> (IsFinite(x[i]) ==> !result[i])
    // Complement property: isnan is complement of (finite or infinite)
    ensures forall i :: 0 <= i < |x| ==> (result[i] <==> !(IsFinite(x[i]) || IsInfinite(x[i])))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement vectorized isnan using IsNaN predicate */
  result := seq i | 0 <= i < |x| => IsNaN(x[i]);
}

// </vc-code>
