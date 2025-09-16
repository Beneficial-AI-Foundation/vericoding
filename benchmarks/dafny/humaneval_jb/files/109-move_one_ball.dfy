// <vc-preamble>
function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)

  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]

  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
