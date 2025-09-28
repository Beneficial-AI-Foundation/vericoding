// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function DoubleElement(x: int): int { 2 * x }
// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Implemented array doubling logic using a loop and helper function. */
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == 2 * s[j]
  {
    result := result + [DoubleElement(s[i])];
    i := i + 1;
  }
}
// </vc-code>
