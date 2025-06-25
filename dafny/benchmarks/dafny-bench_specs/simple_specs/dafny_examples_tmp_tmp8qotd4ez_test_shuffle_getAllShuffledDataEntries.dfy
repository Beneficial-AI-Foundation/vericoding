//ATOM

method swap<T>(a: array<T>, i: int, j: int)
 // requires a != null
 requires 0 <= i < a.Length && 0 <= j < a.Length
 modifies a
 ensures a[i] == old(a[j])
 ensures a[j] == old(a[i])
 ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
 ensures multiset(a[..]) == old(multiset(a[..]))
{
  assume a[i] ==> old(a[j]);
  assume a[j] ==> old(a[i]);
  assume forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  assume multiset(a[..]) ==> old(multiset(a[..]));
}


//ATOM

method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b


// SPEC
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..])
{
}
