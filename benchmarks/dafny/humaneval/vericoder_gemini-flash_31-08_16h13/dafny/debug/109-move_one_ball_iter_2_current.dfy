function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
function rotate_left(a: seq<int>, i: int): seq<int>
  requires 0 <= i < |a|
  ensures |rotate_left(a, i)| == |a|
  ensures forall k :: 0 <= k < |a| ==> rotate_left(a, i)[k] == a[(i + k) % |a|]
{
  a[i..] + a[..i]
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
  can := false;
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !is_sorted(a[k..] + a[..k])
  {
    if i == |a| {
      break;
    }
    var rotated_a := rotate_left(a, i);
    if is_sorted(rotated_a) {
      can := true;
      return;
    }
  }
}
// </vc-code>

