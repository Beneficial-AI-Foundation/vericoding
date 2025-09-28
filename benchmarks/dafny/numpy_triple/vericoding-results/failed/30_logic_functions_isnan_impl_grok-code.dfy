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
/* helper modified by LLM (iteration 5): Fixed syntax by removing 'proof' keyword and removed 'assume false' to avoid verification bypasses */
lemma NaNNotEqual(x: FloatValue)
  requires x.NaN?
  ensures x != x
{
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
  /* code modified by LLM (iteration 5): Removed call to NaNNotEqual lemma since it cannot prove the NaN non-equality property without verification bypasses */
  var i := 0;
  result := [];
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] <==> IsNaN(x[j])
  {
    result := result + [IsNaN(x[i])];
    i := i + 1;
  }
}
// </vc-code>
