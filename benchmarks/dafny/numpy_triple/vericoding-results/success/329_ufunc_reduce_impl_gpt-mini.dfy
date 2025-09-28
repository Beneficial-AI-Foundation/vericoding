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
lemma FoldLeft_unroll(op: (real, real) -> real, arr: seq<real>, start: nat, end: nat)
  requires 0 <= start <= end < |arr|
  ensures start == end || FoldLeft(op, arr, start, end) == op(FoldLeft(op, arr, start, end-1), arr[end])
  decreases end - start
{
  if start == end {
    // nothing to prove
  } else {
    FoldLeft_unroll(op, arr, start, end-1);
    assert FoldLeft(op, arr, start, end) == op(FoldLeft(op, arr, start, end-1), arr[end]);
  }
}

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
  var n := |arr|;
  var i := 1;
  result := arr[0];
  while i < n
    invariant 0 <= i <= n
    invariant result == FoldLeft(op, arr, 0, i-1)
  {
    // Relate the next folded value to the current prefix
    FoldLeft_unroll(op, arr, 0, i);
    result := op(result, arr[i]);
    i := i + 1;
  }
}

// </vc-code>
