// <vc-preamble>
// Helper function to define the left-associative cumulative accumulation
function AccumulateUpTo(a: seq<real>, i: int, op: (real, real) -> real): real
  requires 0 <= i < |a|
  decreases i
{
  if i == 0 then a[0]
  else op(AccumulateUpTo(a, i-1, op), a[i])
}

// Helper function to compute partial accumulation from start to position i
function PartialAccumulate(a: seq<real>, i: int, op: (real, real) -> real): real
  requires 0 <= i < |a|
{
  AccumulateUpTo(a, i, op)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Accumulate(a: seq<real>, op: (real, real) -> real) returns (result: seq<real>)
  // Precondition: works for any sequence
  requires true
  // Postcondition: result has same length as input
  ensures |result| == |a|
  // First element equals first element of input (when non-empty)
  ensures |a| > 0 ==> result[0] == a[0]
  // Recurrence relation: each element is op applied to previous result and current element
  ensures forall i :: 1 <= i < |a| ==> result[i] == op(result[i-1], a[i])
  // Cumulative accumulation property: each element is left-associative fold of all previous elements
  ensures forall i :: 0 <= i < |a| ==> result[i] == AccumulateUpTo(a, i, op)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed return type from array<real> to seq<real> */
{
  var n := |a|;
  if n == 0 {
    return [];
  }

  var newResult: array<real> := new real[n];
  newResult[0] := a[0];
  var i := 1;
  while i < n
    invariant 0 < i <= n
    invariant forall k :: 0 <= k < i ==> newResult[k] == PartialAccumulate(a, k, op)
    invariant forall k :: 0 <= k < i ==> newResult[k] == AccumulateUpTo(a, k, op)
  {
    newResult[i] := op(newResult[i-1], a[i]);
    i := i + 1;
  }
  return newResult[..];
}
// </vc-code>
