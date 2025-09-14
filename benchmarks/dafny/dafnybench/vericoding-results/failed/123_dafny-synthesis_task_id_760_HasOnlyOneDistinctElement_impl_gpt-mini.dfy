

// <vc-helpers>
// No helpers needed
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
    if a.Length == 0 {
      return true;
    }
    assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j];
    return true;
  }
  var first := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == first
  {
    if a[i] != first {
      assert 0 <= i < a.Length;
      assert 0 <= 0 < a.Length;
      assert a[i] != a[0];
      ghost var p := i;
      ghost var q := 0;
      assert 0 <= p < a.Length && 0 <= q < a.Length && a[p] != a[q];
      assert exists p', q' :: 0 <= p' < a.Length && 0 <= q' < a.Length && a[p'] != a[q'];
      return false;
    }
    i := i + 1;
  }
  assert i == a.Length;
  assert forall k :: 0 <= k < a.Length ==> a[k] == first;
  assert forall x, y :: 0 <= x < a.Length && 0 <= y < a.Length ==> a[x] == a[y];
  return true;
}
// </vc-code>

