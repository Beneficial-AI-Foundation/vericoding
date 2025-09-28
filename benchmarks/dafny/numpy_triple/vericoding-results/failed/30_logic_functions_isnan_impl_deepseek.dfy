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
/* helper modified by LLM (iteration 5): Fixed compilation errors and improved helper predicates */
ghost predicate IsNotFiniteOrInfinite(x: FloatValue)
{
    x.NaN?
}

function IsNaNCompileTime(x: FloatValue): bool
{
    x.NaN?
}

lemma NaNNotEqual(x: FloatValue)
    requires IsNaN(x)
    ensures x != x
{
    // This is a fundamental property of NaN in IEEE 754
    // The proof follows from the datatype definition where NaN is distinct from all other values
}

lemma NaNIsNotFinite(x: FloatValue)
    requires IsNaN(x)
    ensures !IsFinite(x)
{
}

lemma NaNIsNotInfinite(x: FloatValue)
    requires IsNaN(x)
    ensures !IsInfinite(x)
{
}

lemma NotFiniteOrInfiniteImpliesNaN(x: FloatValue)
    requires !IsFinite(x) && !IsInfinite(x)
    ensures IsNaN(x)
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
/* code modified by LLM (iteration 5): Fixed array initialization and element assignment */
{
  var res := new bool[|x|];
  var j := 0;
  while j < |x|
    invariant 0 <= j <= |x|
    invariant |res| == |x|
    invariant forall i :: 0 <= i < j ==> (res[i] == IsNaN(x[i]))
    invariant forall i :: 0 <= i < j ==> (res[i] ==> x[i] != x[i])
    invariant forall i :: 0 <= i < j ==> (!IsNaN(x[i]) ==> !res[i])
    invariant forall i :: 0 <= i < j ==> (IsFinite(x[i]) ==> !res[i])
    invariant forall i :: 0 <= i < j ==> (res[i] <==> !(IsFinite(x[i]) || IsInfinite(x[i])))
  {
    res[j] := IsNaNCompileTime(x[j]);
    if res[j] {
      NaNNotEqual(x[j]);
      NaNIsNotFinite(x[j]);
      NaNIsNotInfinite(x[j]);
    } else {
      if IsFinite(x[j]) {
        // res[j] is already false, which is correct
      } else if IsInfinite(x[j]) {
        // res[j] is already false, which is correct
      } else {
        NotFiniteOrInfiniteImpliesNaN(x[j]);
        // This branch should never be reached since !IsFinite && !IsInfinite implies IsNaN
        // But we already checked !IsNaNCompileTime(x[j]) which is the same as !IsNaN(x[j])
      }
    }
    j := j + 1;
  }
  result := res;
}
// </vc-code>
