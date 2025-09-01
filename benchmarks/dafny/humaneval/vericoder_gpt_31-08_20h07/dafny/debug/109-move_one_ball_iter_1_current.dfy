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
  var n := |a|;
  var i := 0;
  can := false;
  while i < n
    invariant 0 <= i <= n
    invariant can ==> exists j :: 0 <= j < i && is_sorted(a[j..] + a[..j])
    invariant !can ==> forall j :: 0 <= j < i ==> !is_sorted(a[j..] + a[..j])
    decreases n - i
  {
    if is_sorted(a[i..] + a[..i]) {
      can := true;
    }
    i := i + 1;
  }
}
// </vc-code>

