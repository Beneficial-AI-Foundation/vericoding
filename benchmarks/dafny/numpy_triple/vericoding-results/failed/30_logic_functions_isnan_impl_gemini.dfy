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
lemma NanIsComplementOfFiniteOrInfinite(f: FloatValue)
    ensures IsNaN(f) <==> !(IsFinite(f) || IsInfinite(f))
{
    match f {
        case Finite(_) =>
        case NaN =>
        case PosInf =>
        case NegInf =>
    }
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
  var r := new bool[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> (r[j] <==> IsNaN(x[j]))
    invariant forall j :: 0 <= j < i ==> (r[j] <==> !(IsFinite(x[j]) || IsInfinite(x[j])))
    invariant forall j :: 0 <= j < i ==> (r[j] ==> x[j] != x[j])
    invariant forall j :: 0 <= j < i ==> (!IsNaN(x[j]) ==> !r[j])
    invariant forall j :: 0 <= j < i ==> (IsFinite(x[j]) ==> !r[j])
  {
    var v := x[i];
    r[i] := v.NaN?;
    NanIsComplementOfFiniteOrInfinite(v);
    i := i + 1;
  }
  result := r[..];
}
// </vc-code>
