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
/* helper modified by LLM (iteration 5): The helper function `IsNaN_func` is already correct and does not need further modification. */
function IsNaN_func(x: FloatValue): bool
{
    x.NaN?
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
/* code modified by LLM (iteration 5): Fixed loop bound from `|x| - 1` to `|x|` and then adjusted indices for `result_seq` to address `lower bound must not exceed upper bound` compiler error; initialized `result_seq` to a sequence of `false` values of the correct length to satisfy postconditions related to sequence length and element values; updated loop to correctly populate `result_seq` according to `IsNaN_func`. */
{
  var result_seq: seq<bool> := new bool[|x|](i => false);
  for i := 0 to |x| {
    if (i < |x|) {
      result_seq := result_seq[i := IsNaN_func(x[i])];
    }
  }
  return result_seq;
}
// </vc-code>
