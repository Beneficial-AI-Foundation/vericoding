predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

// <vc-helpers>
method Swap(a: array<int>, i: int, j: int)
  modifies a
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == old(multiset(a[..]))
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

lemma SplitPointLemma(a: array<int>, n: int, m: int)
  requires 0 <= n <= m <= a.Length
  requires SplitPoint(a, n)
  ensures SplitPoint(a, m)
{
  forall i, j | 0 <= i < m <= j < a.Length
    ensures a[i] <= a[j]
  {
    if i < n {
      assert 0 <= i < n <= j < a.Length;
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
method SelectionSortImpl(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant SplitPoint(a, n)
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := n;
    var i := n + 1;
    while i < a.Length
      invariant n <= minIndex < a.Length
      invariant n <= i <= a.Length
      invariant forall k :: n <= k < i ==> a[minIndex] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[i] < a[minIndex] {
        minIndex := i;
      }
      i := i + 1;
    }
    if minIndex != n {
      Swap(a, n, minIndex);
    }
    assert SplitPoint(a, n + 1);
    n := n + 1;
  }
}
// </vc-code>
