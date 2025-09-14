

// <vc-helpers>
lemma SortedImpliesAllPairs(a: array<int>)
    requires a.Length > 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures forall k, l :: 0 <= k < l < a.Length ==> a[k] <= a[l]
{
}

lemma NotSortedImpliesExistsPair(a: array<int>)
    requires a.Length > 0
    requires exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
    ensures exists m, n :: 0 <= m < n < a.Length && a[m] > a[n]
{
}
// </vc-helpers>

// <vc-spec>
method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
// </vc-spec>
// <vc-code>
{
  sorted := true;
  var k := 0;
  while k < a.Length - 1
    invariant 0 <= k <= a.Length - 1
    invariant sorted <== forall i, j :: 0 <= i < j <= k ==> a[i] <= a[j]
    invariant !sorted ==> exists i, j :: 0 <= i < j <= k && a[i] > a[j]
  {
    if a[k] > a[k + 1] {
      sorted := false;
      break;
    }
    k := k + 1;
  }
}
// </vc-code>

