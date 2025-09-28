// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): bitwise and helper */
function OpAnd(x: bv32, y: bv32): bv32 { x & y }
// </vc-helpers>

// <vc-spec>
method BitwiseAnd(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement elementwise bitwise and with loop and invariants */
  var arr := new bv32[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i && i <= |a|
    invariant arr.Length == |a|
    invariant forall j :: 0 <= j < i ==> arr[j] == OpAnd(a[j], b[j])
    decreases |a| - i
  {
    arr[i] := OpAnd(a[i], b[i]);
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
