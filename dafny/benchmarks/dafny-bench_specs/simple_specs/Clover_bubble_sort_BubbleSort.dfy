// SPEC
method BubbleSort(a: array<int>)
 modifies a
 ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
 ensures multiset(a[..])==multiset(old(a[..]))
{
}
