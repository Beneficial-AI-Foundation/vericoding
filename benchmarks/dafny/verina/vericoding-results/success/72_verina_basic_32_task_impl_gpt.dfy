// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SwapEnds(a: seq<int>): seq<int>
  requires |a| > 0
  ensures |SwapEnds(a)| == |a|
  ensures SwapEnds(a)[0] == a[|a| - 1]
  ensures SwapEnds(a)[|a| - 1] == a[0]
  ensures forall i :: 1 <= i < |a| - 1 ==> SwapEnds(a)[i] == a[i]
{
  a[0 := a[|a| - 1]][|a| - 1 := a[0]]
}
// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |result| == |a|
    ensures result[0] == a[|a| - 1]
    ensures result[|result| - 1] == a[0]
    ensures forall i :: 1 <= i < |result| - 1 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := SwapEnds(a);
}
// </vc-code>
