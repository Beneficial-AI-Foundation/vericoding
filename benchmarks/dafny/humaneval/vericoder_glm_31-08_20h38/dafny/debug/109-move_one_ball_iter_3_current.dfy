function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)
  // pre-conditions-start
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  can := false;
  for i := 0 to |a|
  {
    if is_sorted(a[i..] + a[..i]) {
      can := true;
      break;
    }
  }
}
// </vc-code>

