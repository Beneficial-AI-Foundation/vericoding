// <vc-preamble>
function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): rewrote function to be recursive, avoiding a quantifier warning */
function CountInternalDescents(s: seq<int>): nat
{
  if |s| <= 1 then 0
  else (if s[0] > s[1] then 1 else 0) + CountInternalDescents(s[1..])
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
  /* code modified by LLM (iteration 3): No logic change needed, as the implementation already verifies. The compilation issue was in the helpers section. */
  can := false;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant can <==> (exists j :: 0 <= j < i && is_sorted(a[j..] + a[..j]))
  {
    if is_sorted(a[i..] + a[..i]) {
      can := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
