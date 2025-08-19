predicate sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {
    forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
  }

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>