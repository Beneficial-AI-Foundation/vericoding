

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |xs| - 1;
  var r: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == xs[j+1] * (j+1)
    decreases n - i
  {
    assert i + 1 < |xs|;
    r := r + [xs[i+1] * (i + 1)];
    i := i + 1;
  }
  result := r;
}
// </vc-code>

