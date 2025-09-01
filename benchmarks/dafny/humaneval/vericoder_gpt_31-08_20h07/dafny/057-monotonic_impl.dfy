

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var inc := (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]);
  var dec := (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]);
  result := inc || dec;
}
// </vc-code>

