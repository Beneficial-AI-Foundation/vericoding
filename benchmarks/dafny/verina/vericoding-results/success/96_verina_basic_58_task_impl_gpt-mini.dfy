// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Double(x: int): int { 2 * x }
// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == 2 * s[j]
  {
    result := result + [Double(s[i])];
    i := i + 1;
  }
}
// </vc-code>
