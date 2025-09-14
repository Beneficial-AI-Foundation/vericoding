

// <vc-helpers>
lemma AllEqualToValImpliesPairwise(a: array?<int>, v: int)
  requires a != null
  requires forall k :: 0 <= k < a.Length ==> a[k] == v
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
{
  forall i: int, j: int | 0 <= i < a.Length && 0 <= j < a.Length
    ensures a[i] == a[j]
  {
    assert a[i] == v;
    assert a[j] == v;
  }
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return true;
  }
  var v := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == v
  {
    if a[i] != v {
      assert 0 <= i < a.Length;
      assert 0 < a.Length;
      assert a[i] != a[0];
      return false;
    }
    i := i + 1;
  }
  assert i == a.Length;
  assert forall k :: 0 <= k < a.Length ==> a[k] == v;
  AllEqualToValImpliesPairwise(a, v);
  return true;
}
// </vc-code>

