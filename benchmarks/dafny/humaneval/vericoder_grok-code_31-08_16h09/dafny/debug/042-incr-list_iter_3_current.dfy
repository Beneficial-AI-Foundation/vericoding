

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == l[k] + 1
  {
    res := res + [l[i] + 1];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

