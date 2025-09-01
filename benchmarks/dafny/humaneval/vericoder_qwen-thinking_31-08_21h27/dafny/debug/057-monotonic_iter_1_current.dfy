

// <vc-helpers>

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
  return (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i+1]) || (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i+1]);
}
// </vc-code>

