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
lemma AccumulateUpToStep(a: seq<real>, i: int, op: (real, real) -> real)
  requires 0 < i < |a|
  ensures AccumulateUpTo(a, i, op) == op(AccumulateUpTo(a, i-1, op), a[i])
{
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
  var n := |a|;
  if n == 0 {
    result := [];
  } else {
    var r: seq<real> := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |r| == i
      invariant i == 0 ==> r == []
      invariant i > 0 ==> r[0] == a[0]
      invariant forall j :: 1 <= j < i ==> r[j] == op(r[j-1], a[j])
      invariant forall j :: 0 <= j < i ==> r[j] == AccumulateUpTo(a, j, op)
    {
      var next: real;
      if i == 0 {
        next := a[0];
        assert AccumulateUpTo(a, 0, op) == a[0];
        assert next == AccumulateUpTo(a, 0, op);
      } else {
        next := op(r[i-1], a[i]);
        AccumulateUpToStep(a, i, op);
        assert r[i-1] == AccumulateUpTo(a, i-1, op);
        assert AccumulateUpTo(a, i, op) == op(AccumulateUpTo(a, i-1, op), a[i]);
        assert next == op(r[i-1], a[i]);
        assert next == AccumulateUpTo(a, i, op);
      }
      r := r + [next];
      i := i + 1;
    }
    result := r;
  }
}
// </vc-code>
