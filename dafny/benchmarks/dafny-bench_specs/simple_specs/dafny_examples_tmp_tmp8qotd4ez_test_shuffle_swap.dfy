// SPEC

method swap<T>(a: array<T>, i: int, j: int)
 // requires a != null
 requires 0 <= i < a.Length && 0 <= j < a.Length
 modifies a
 ensures a[i] == old(a[j])
 ensures a[j] == old(a[i])
 ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
 ensures multiset(a[..]) == old(multiset(a[..]))
{
}
