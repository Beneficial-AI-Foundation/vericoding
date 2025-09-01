

// <vc-helpers>
lemma ForallTransitiveIncrease(xs: seq<int>, i: int)
  requires 0 <= i < |xs| -1
  requires forall k, l :: 0 <= k < l <= i + 1 ==> xs[k] < xs[l]
  ensures forall k, l :: 0 <= k < l <= i + 2 && l < |xs| ==> xs[k] < xs[l]
{
  if i + 2 < |xs| {
    // We need to show that xs[i+1] < xs[i+2]
    // And also that for any k <= i, xs[k] < xs[i+2]
    assert forall k, l :: 0 <= k < l <= i + 1 ==> xs[k] < xs[l];
  }
}

lemma ForallTransitiveDecrease(xs: seq<int>, i: int)
  requires 0 <= i < |xs| -1
  requires forall k, l :: 0 <= k < l <= i + 1 ==> xs[k] > xs[l]
  ensures forall k, l :: 0 <= k < l <= i + 2 && l < |xs| ==> xs[k] > xs[l]
{
  if i + 2 < |xs| {
    // Same logic as ForallTransitiveIncrease
    assert forall k, l :: 0 <= k < l <= i + 1 ==> xs[k] > xs[l];
  }
}
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
  if |xs| <= 1 {
    return true;
  }

  var increasing: bool := true;
  var decreasing: bool := true;

  for i := 0 to |xs| - 2
    invariant 0 <= i <= |xs| - 1
    invariant increasing ==> (forall k, l :: 0 <= k < l < i + 1 ==> xs[k] < xs[l])
    invariant decreasing ==> (forall k, l :: 0 <= k < l < i + 1 ==> xs[k] > xs[l])
    invariant increasing ==> (forall k :: 0 <= k < i ==> xs[k] < xs[k+1])
    invariant decreasing ==> (forall k :: 0 <= k < i ==> xs[k] > xs[k+1])
    invariant increasing ==> (forall k, l :: 0 <= k < l < i + 1 && l < |xs| ==> xs[k] < xs[l])
    invariant decreasing ==> (forall k, l :: 0 <= k < l < i + 1 && l < |xs| ==> xs[k] > xs[l])
  {
    if xs[i] >= xs[i+1] {
      increasing := false;
    }
    if xs[i] <= xs[i+1] {
      decreasing := false;
    }
  }

  // After the loop, the invariants hold for i = |xs| - 1.
  // We need to prove the postcondition based on these invariants.

  if increasing {
    assert forall k, l :: 0 <= k < l < |xs| ==> xs[k] < xs[l];
  }
  if decreasing {
    assert forall k, l :: 0 <= k < l < |xs| ==> xs[k] > xs[l];
  }

  return increasing || decreasing;
}
// </vc-code>

