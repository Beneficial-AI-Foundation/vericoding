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
/* helper modified by LLM (iteration 2): Removed incorrect lemma, no helpers needed */
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
  /* code modified by LLM (iteration 2): Fixed iterative computation of FoldLeft */
  result := arr[0];
  var i := 1;
  
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant result == FoldLeft(op, arr, 0, i-1)
  {
    // By definition of FoldLeft:
    // FoldLeft(op, arr, 0, i) = op(FoldLeft(op, arr, 0, i-1), arr[i])
    // Since result == FoldLeft(op, arr, 0, i-1), we have:
    result := op(result, arr[i]);
    i := i + 1;
  }
}
// </vc-code>
