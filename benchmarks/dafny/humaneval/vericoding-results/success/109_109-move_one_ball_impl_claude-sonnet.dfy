// <vc-preamble>
function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added proof content to lemmas */
function can_sort_with_rotation(a: seq<int>, start: int): bool
  requires 0 <= start < |a|
{
  is_sorted(a[start..] + a[..start])
}

lemma rotation_preserves_elements(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures multiset(a[i..] + a[..i]) == multiset(a)
{
  assert a[i..] + a[..i] == a[i..] + a[0..i];
  assert multiset(a[i..]) + multiset(a[0..i]) == multiset(a[0..i]) + multiset(a[i..]);
  assert multiset(a[0..i]) + multiset(a[i..]) == multiset(a[0..i] + a[i..]);
  assert a[0..i] + a[i..] == a[0..];
  assert a[0..] == a;
}

lemma sorted_rotation_exists_iff_condition(a: seq<int>)
  requires |a| > 0
  ensures (exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])) <==> (exists i :: 0 <= i < |a| && can_sort_with_rotation(a, i))
{
  if exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i]) {
    var k :| 0 <= k < |a| && is_sorted(a[k..] + a[..k]);
    assert can_sort_with_rotation(a, k);
  }
  if exists i :: 0 <= i < |a| && can_sort_with_rotation(a, i) {
    var k :| 0 <= k < |a| && can_sort_with_rotation(a, k);
    assert is_sorted(a[k..] + a[..k]);
  }
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
  /* code modified by LLM (iteration 2): Fixed loop invariant and added found flag tracking */
  var i := 0;
  var found := false;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant found <==> exists k :: 0 <= k < i && is_sorted(a[k..] + a[..k])
  {
    var rotated := a[i..] + a[..i];
    if is_sorted(rotated) {
      found := true;
    }
    i := i + 1;
  }
  can := found;
}
// </vc-code>
