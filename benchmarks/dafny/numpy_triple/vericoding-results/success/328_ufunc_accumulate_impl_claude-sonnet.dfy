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
/* helper modified by LLM (iteration 2): added lemma to prove recurrence relation maintains AccumulateUpTo property */
lemma AccumulateRecurrence(a: seq<real>, i: int, op: (real, real) -> real, result: seq<real>)
  requires 0 <= i < |a|
  requires |result| > i
  requires i == 0 ==> result[0] == a[0]
  requires i > 0 ==> result[i] == op(result[i-1], a[i])
  requires forall j :: 0 <= j < i ==> result[j] == AccumulateUpTo(a, j, op)
  ensures result[i] == AccumulateUpTo(a, i, op)
{
  if i == 0 {
    // Base case: result[0] == a[0] == AccumulateUpTo(a, 0, op)
  } else {
    // Inductive case: result[i] == op(result[i-1], a[i]) == op(AccumulateUpTo(a, i-1, op), a[i]) == AccumulateUpTo(a, i, op)
  }
}
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
{
  /* code modified by LLM (iteration 2): fixed array/sequence type mismatch */
  if |a| == 0 {
    result := [];
    return;
  }
  
  var temp := new real[|a|];
  temp[0] := a[0];
  
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant temp[0] == a[0]
    invariant forall j :: 1 <= j < i ==> temp[j] == op(temp[j-1], a[j])
    invariant forall j :: 0 <= j < i ==> temp[j] == AccumulateUpTo(a, j, op)
  {
    temp[i] := op(temp[i-1], a[i]);
    AccumulateRecurrence(a, i, op, temp[..]);
    i := i + 1;
  }
  
  result := temp[..];
}
// </vc-code>
