function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
function rotate_left(a: seq<int>, i: int) : seq<int}
  requires 0 <= i <= |a|
  ensures |rotate_left(a, i)} == |a|
{
  a[i..] + a[..i]
}

function is_rotated_sorted(a: seq<int}) : bool
{
  exists i :: 0 <= i < |a| && is_sorted(rotate_left(a, i))
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
  can := is_rotated_sorted(a);
}
// </vc-code>

