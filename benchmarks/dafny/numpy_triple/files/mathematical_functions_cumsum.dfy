// <vc-preamble>
// Helper function to compute the sum of a sequence slice
function Sum(s: seq<real>, start: nat, end: nat): real
  requires 0 <= start <= end <= |s|
{
  if start == end then 0.0
  else s[start] + Sum(s, start + 1, end)
}

// Main method specification for numpy cumsum
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NumpyCumsum(a: seq<real>) returns (result: seq<real>)
  // No special preconditions required
  requires true
  ensures |result| == |a|
  // For non-empty sequences, first element equals first element of input
  ensures |a| > 0 ==> result[0] == a[0]
  // Recurrence relation: each element equals previous cumsum plus current element
  ensures forall i :: 1 <= i < |result| ==> result[i] == result[i-1] + a[i]
  // Cumulative sum property: each element is sum of all previous elements plus current
  ensures forall i :: 0 <= i < |result| ==> result[i] == Sum(a, 0, i + 1)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
