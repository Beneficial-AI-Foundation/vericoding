// <vc-preamble>
// Helper function to define left-associative folding
function FoldLeft(op: (real, real) -> real, arr: seq<real>, start: nat, end: nat): real
  requires 0 <= start <= end < |arr|
  decreases end - start
{
  if start == end then arr[start]
  else op(FoldLeft(op, arr, start, end-1), arr[end])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reduce(op: (real, real) -> real, arr: seq<real>) returns (result: real)
  // Array must be non-empty
  requires |arr| > 0
  
  // Result is the left-associative application of op over all elements
  ensures result == FoldLeft(op, arr, 0, |arr|-1)
  
  // For single element arrays, result equals that element
  ensures |arr| == 1 ==> result == arr[0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
