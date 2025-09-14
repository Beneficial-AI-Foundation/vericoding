// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function dropFront(a: seq<int>): seq<int>
    requires |a| > 0
    ensures |dropFront(a)| == |a| - 1
    ensures forall i :: 0 <= i < |dropFront(a)| ==> dropFront(a)[i] == a[i + 1]
{
  a[1..]
}
// </vc-helpers>

// <vc-spec>
method RemoveFront(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |a| > 0
    ensures |result| == |a| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  result := dropFront(a);
}
// </vc-code>
