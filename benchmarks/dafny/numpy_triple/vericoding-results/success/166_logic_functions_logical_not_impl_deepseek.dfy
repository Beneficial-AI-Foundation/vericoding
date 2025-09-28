// <vc-preamble>
/**
 * Computes the logical NOT of each element in the input sequence according to NumPy semantics.
 * Uses NumPy's truthiness convention: zero is falsy (NOT zero = true), 
 * all non-zero values are truthy (NOT non-zero = false).
 */
// </vc-preamble>

// <vc-helpers>
function IsZero(r: real): bool { r == 0.0 }
/* helper modified by LLM (iteration 3): Fixed type compatibility issue */
// </vc-helpers>

// <vc-spec>
method LogicalNot(x: seq<real>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed array/seq type mismatch by using sequence construction */
  result := [];
  var idx := 0;
  while idx < |x|
    invariant 0 <= idx <= |x|
    invariant |result| == idx
    invariant forall i :: 0 <= i < idx ==> result[i] == (x[i] == 0.0)
  {
    result := result + [IsZero(x[idx])];
    idx := idx + 1;
  }
}
// </vc-code>
