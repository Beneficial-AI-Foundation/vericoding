function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
lemma rotation_preserves_elements(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures multiset(a[i..] + a[..i]) == multiset(a)
{
}

lemma check_all_rotations_complete(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> (a[i..] + a[..i] == a[i..] + a[0..i])
{
}
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
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !is_sorted(a[k..] + a[..k])
  {
    var rotated := a[i..] + a[..i];
    if is_sorted(rotated) {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

