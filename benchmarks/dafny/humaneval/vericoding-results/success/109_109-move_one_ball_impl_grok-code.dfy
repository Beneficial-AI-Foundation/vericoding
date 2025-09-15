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
/* code modified by LLM (iteration 3): adjusted loop invariants to establish can <==> exists rotation is sorted */
{
  var n := |a|;
  can := false;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant can ==> exists j :: 0 <= j < i && is_sorted(a[j..] + a[..j])
    invariant !can ==> forall j :: 0 <= j < i ==> !is_sorted(a[j..] + a[..j])
  {
    var rotated := a[i..] + a[..i];
    if !can && is_sorted(rotated) {
      can := true;
    }
  }
}
// </vc-code>
