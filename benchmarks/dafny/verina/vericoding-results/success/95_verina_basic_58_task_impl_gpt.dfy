// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple integer doubling function used by implementation if needed */
function DoubleOf(x: int): int { 2 * x }
// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fill an array with doubled elements and convert to sequence */
  var n := |s|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == 2 * s[j]
  {
    a[i] := DoubleOf(s[i]);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
