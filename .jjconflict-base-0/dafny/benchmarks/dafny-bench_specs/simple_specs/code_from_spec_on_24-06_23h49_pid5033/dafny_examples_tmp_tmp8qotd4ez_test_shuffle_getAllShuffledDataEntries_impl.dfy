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
  assume a[i] == old(a[j]);
  assume a[j] == old(a[i]);
  assume forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  assume multiset(a[..]) == old(multiset(a[..]));
}


//ATOM

method random(a: int, b: int) returns (r: int)
 requires a <= b
 ensures a <= b ==> a <= r <= b
{
}


//IMPL getAllShuffledDataEntries
 
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..])
{
  result := new T[m_dataEntries.Length];
  
  if m_dataEntries.Length == 0 {
    return;
  }
  
  // Copy all elements from input to result
  var i := 0;
  while i < m_dataEntries.Length
    invariant 0 <= i <= m_dataEntries.Length
    invariant forall k :: 0 <= k < i ==> result[k] == m_dataEntries[k]
    /* code modified by LLM (iteration 1): Added multiset invariant for copying phase */
    invariant multiset(result[..i]) == multiset(m_dataEntries[..i])
  {
    result[i] := m_dataEntries[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to establish multiset equality after copying */
  assert multiset(result[..]) == multiset(m_dataEntries[..]);
  
  // Shuffle using Fisher-Yates algorithm
  var j := m_dataEntries.Length - 1;
  while j > 0
    /* code modified by LLM (iteration 1): Fixed bounds invariant and added length check */
    invariant 0 <= j < m_dataEntries.Length
    invariant result.Length == m_dataEntries.Length
    invariant multiset(result[..]) == multiset(m_dataEntries[..])
  {
    /* code modified by LLM (iteration 1): Fixed random call parameters and added bounds checking */
    var randIdx := random(0, j);
    /* code modified by LLM (iteration 1): Added assertions to ensure indices are valid for swap */
    assert 0 <= randIdx <= j < m_dataEntries.Length;
    assert randIdx < result.Length;
    assert j < result.Length;
    swap(result, j, randIdx);
    j := j - 1;
  }
}