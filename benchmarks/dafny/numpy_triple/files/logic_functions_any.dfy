// <vc-preamble>
datatype Float = 
  | Value(r: real)
  | NaN
  | PosInf
  | NegInf

function IsTruthy(f: Float): bool
{
  match f
    case Value(r) => r != 0.0
    case NaN => false
    case PosInf => true
    case NegInf => true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Any<n: nat>(v: seq<Float>) returns (result: bool)
  requires |v| == n
  // Test whether any element in the sequence evaluates to True (non-zero)
  ensures result == true <==> exists i :: 0 <= i < |v| && IsTruthy(v[i])
  // Equivalent: result is false iff all elements are falsy
  ensures result == false <==> forall i :: 0 <= i < |v| ==> !IsTruthy(v[i])
  // Empty sequence returns false
  ensures |v| == 0 ==> result == false
  // If all elements are falsy, result must be false
  ensures (forall i :: 0 <= i < |v| ==> !IsTruthy(v[i])) ==> result == false
  // If any element is truthy, result must be true
  ensures (exists i :: 0 <= i < |v| && IsTruthy(v[i])) ==> result == true
  // Logical consistency - result is either true or false, never both
  ensures result == true || result == false
  ensures !(result == true && result == false)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
