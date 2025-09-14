// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Middle(a: seq<int>): seq<int> {
  if |a| <= 2 then [] else a[1..|a|-1]
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
  if |a| == 1 {
    result := a;
  } else {
    var n := |a|;
    result := [a[n-1]] + a[1..n-1] + [a[0]];
  }
}
// </vc-code>
