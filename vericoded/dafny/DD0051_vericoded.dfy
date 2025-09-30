

// <vc-helpers>
method Swap(a: array?<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  ghost var ms0 := multiset(a[..]);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..]) == ms0
    invariant forall p,q :: 0 <= p < q < i ==> a[p] <= a[q]
    invariant forall p,q :: 0 <= p < i <= q < n ==> a[p] <= a[q]
  {
    var m := i;
    var j := i + 1;
    while j < n
      invariant i+1 <= j <= n
      invariant i <= m < j
      invariant forall k :: i <= k < j ==> a[m] <= a[k]
      invariant multiset(a[..]) == ms0
      invariant forall p :: 0 <= p < i ==> a[p] <= a[m]
    {
      if a[j] < a[m] {
        m := j;
      }
      j := j + 1;
    }
    assert forall p :: 0 <= p < i ==> a[p] <= a[m];
    if m != i {
      Swap(a, i, m);
    }
    i := i + 1;
  }
}
// </vc-code>

