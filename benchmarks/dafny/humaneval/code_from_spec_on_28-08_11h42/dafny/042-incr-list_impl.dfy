// <vc-helpers>
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
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == l[j] + 1
  {
    result := result + [l[i] + 1];
    i := i + 1;
  }
}
// </vc-code>
