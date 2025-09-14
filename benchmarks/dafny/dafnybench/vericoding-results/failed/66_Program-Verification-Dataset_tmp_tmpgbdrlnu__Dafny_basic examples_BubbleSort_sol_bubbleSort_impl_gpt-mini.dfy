predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
method Swap(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted_between(a, 0, i)
    invariant forall k, t :: 0 <= k < i && i <= t < n ==> a[k] <= a[t]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var m := i;
    var j := i + 1;
    while j < n
      invariant i <= m < n
      invariant i + 1 <= j <= n
      invariant forall u :: i <= u < j ==> a[m] <= a[u]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] < a[m] {
        m := j;
      }
      j := j + 1;
    }
    // at loop exit j == n
    assert j == n;
    // m is minimal index in [i, n)
    assert forall u :: i <= u < n ==> a[m] <= a[u];
    // elements in prefix are <= a[m]
    assert forall k :: 0 <= k < i ==> a[k] <= a[m];
    ghost var minValue := a[m];
    // perform swap via helper to preserve multiset information
    Swap(a, i, m);
    assert a[i] == minValue;
    // now prefix elements <= new a[i]
    assert forall k :: 0 <= k < i ==> a[k] <= a[i];
    // combine prefix sorted and comparisons to extend sorted_between to i+1
    assert sorted_between(a, 0, i+1);
    i := i + 1;
  }
}
// </vc-code>

