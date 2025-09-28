// <vc-preamble>
/**
 * Computes the logical NOT of each element in the input sequence according to NumPy semantics.
 * Uses NumPy's truthiness convention: zero is falsy (NOT zero = true), 
 * all non-zero values are truthy (NOT non-zero = false).
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' and defined logical NOT per NumPy truthiness */
function LogicalNotElem(v: real): bool
  ensures LogicalNotElem(v) == (v == 0.0)
{
  v == 0.0
}
// </vc-helpers>

// <vc-spec>
method LogicalNot(x: seq<real>) returns (result: seq<bool>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement loop constructing result using helper */
  var r: seq<bool> := [];
  var i: int := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> r[k] == (x[k] == 0.0)
    decreases |x| - i
  {
    r := r + [LogicalNotElem(x[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
