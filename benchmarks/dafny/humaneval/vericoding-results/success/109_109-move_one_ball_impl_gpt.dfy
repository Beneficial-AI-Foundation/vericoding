// <vc-preamble>
function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): introduced predicate capturing the ensures condition */
predicate HasSortedRotation(a: seq<int>)
{
  exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
}
// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)

  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]

  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute condition via helper predicate without extra assumptions */
  can := HasSortedRotation(a);
}
// </vc-code>
