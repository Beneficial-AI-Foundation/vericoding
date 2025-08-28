// <vc-helpers>
// Helper lemma to prove uniqueness in a sequence
lemma UniqueElements(s: seq<int>, idx: int)
  requires 0 <= idx < |s|
  ensures forall i :: 0 <= i < idx ==> s[i] != s[idx]
{
  if idx > 0 {
    UniqueElements(s, idx - 1);
    assert forall i :: 0 <= i < idx - 1 ==> s[i] != s[idx - 1];
    assert s[idx - 1] != s[idx]; // This assertion helps bridge the gap
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method DifferenceImpl(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
  ensures forall x :: x in diff <==> (x in a && x !in b)
  ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{
  diff := [];
  for i := 0 to |a|
    invariant forall x :: x in diff <==> (exists k :: 0 <= k < i && a[k] == x && x !in b)
    invariant forall m, n :: 0 <= m < n < |diff| ==> diff[m] != diff[n]
  {
    if i < |a| && a[i] !in b && a[i] !in diff {
      diff := diff + [a[i]];
      // Assert uniqueness for the newly added element
      assert forall k :: 0 <= k < |diff| - 1 ==> diff[k] != a[i];
      UniqueElements(diff, |diff| - 1);
    }
  }
}
// </vc-code>
