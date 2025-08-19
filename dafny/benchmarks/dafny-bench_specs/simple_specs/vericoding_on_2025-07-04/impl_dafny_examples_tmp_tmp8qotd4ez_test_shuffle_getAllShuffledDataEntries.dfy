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
 ensures a <= r <= b
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
  
  // Copy all elements from input to result
  var i := 0;
  while i < m_dataEntries.Length
    invariant 0 <= i <= m_dataEntries.Length
    /* code modified by LLM (iteration 1): added invariant to track copied elements */
    invariant forall k :: 0 <= k < i ==> result[k] == m_dataEntries[k]
  {
    result[i] := m_dataEntries[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion to establish array equality after copying */
  assert forall k :: 0 <= k < result.Length ==> result[k] == m_dataEntries[k];
  assert result[..] == m_dataEntries[..];
  
  // Shuffle the result array using Fisher-Yates shuffle
  var j := result.Length - 1;
  while j > 0
    invariant 0 <= j < result.Length
    /* code modified by LLM (iteration 1): maintained multiset invariant throughout shuffle */
    invariant multiset(result[..]) == multiset(m_dataEntries[..])
  {
    var randomIndex := random(0, j);
    /* code modified by LLM (iteration 1): added proper bounds checking for swap operation */
    assert 0 <= randomIndex <= j < result.Length;
    swap(result, j, randomIndex);
    j := j - 1;
  }
}