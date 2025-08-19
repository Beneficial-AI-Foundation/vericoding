method swap<T>(a: array<T>, i: int, j: int)
 // requires a != null
 requires 0 <= i < a.Length && 0 <= j < a.Length
 modifies a
 ensures a[i] == old(a[j])
 ensures a[j] == old(a[i])
 ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
 ensures multiset(a[..]) == old(multiset(a[..]))
{
  /* code modified by LLM (iteration 1): replaced assume statements with actual swap implementation */
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}


//ATOM

method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b
{
  /* code modified by LLM (iteration 1): added body to make method compilable */
  if a <= b {
    r := a;
  } else {
    r := 0;
  }
}


//IMPL

method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..])
{
  result := new T[m_dataEntries.Length];
  
  var i := 0;
  while i < m_dataEntries.Length
    invariant 0 <= i <= m_dataEntries.Length
    invariant result.Length == m_dataEntries.Length
    invariant forall k :: 0 <= k < i ==> result[k] == m_dataEntries[k]
    /* code modified by LLM (iteration 1): added multiset invariant to establish the property for the second loop */
    invariant multiset(result[0..i]) == multiset(m_dataEntries[0..i])
  {
    result[i] := m_dataEntries[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion to help prove multiset equality after first loop */
  assert result[..] == m_dataEntries[..];
  assert multiset(result[..]) == multiset(m_dataEntries[..]);
  
  var j := 0;
  while j < result.Length
    invariant 0 <= j <= result.Length
    invariant result.Length == m_dataEntries.Length
    invariant multiset(result[..]) == multiset(m_dataEntries[..])
  {
    if result.Length > 1 {
      var randomIndex := random(0, result.Length - 1);
      if 0 <= randomIndex < result.Length && randomIndex != j {
        swap(result, j, randomIndex);
      }
    }
    j := j + 1;
  }
}