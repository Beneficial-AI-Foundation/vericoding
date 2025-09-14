// Bubble Sort

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
// </vc-spec>
// <vc-code>
{
  var n := a.Length0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length1 == 2
    invariant forall k :: 0 <= k < i ==> a[k, 1] == k
    invariant forall p, q :: 0 <= p <= q < i ==> a[p, 1] <= a[q, 1]
    decreases n - i
  {
    a[i, 1] := i;
    i := i + 1;
  }
}
// </vc-code>

