

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  var acc := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |acc| == i
    invariant forall k :: 0 <= k < i ==> acc[k] == a[k] + b[k]
  {
    acc := acc + [a[i] + b[i]];
    i := i + 1;
  }
  return acc;
}
// </vc-code>

