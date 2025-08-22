//IMPL BubbleSort
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> a[k1] <= a[k2]
    invariant forall k1, k2 :: 0 <= k1 < i && i <= k2 < n ==> a[k1] <= a[k2]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := n - 1;
    while j > i
      invariant i <= j < n
      invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> a[k1] <= a[k2]
      invariant forall k1, k2 :: 0 <= k1 < i && i <= k2 < n ==> a[k1] <= a[k2]
      invariant forall k :: j < k < n ==> a[j] <= a[k]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j-1] > a[j] {
        a[j-1], a[j] := a[j], a[j-1];
      }
      j := j - 1;
    }
    i := i + 1;
  }
}