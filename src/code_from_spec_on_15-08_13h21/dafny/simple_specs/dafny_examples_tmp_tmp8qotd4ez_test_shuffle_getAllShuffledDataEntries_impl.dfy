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
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

//ATOM
method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b

//IMPL getAllShuffledDataEntries
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
 // requires m_dataEntries != null
 // ensures result != null
 ensures result.Length == m_dataEntries.Length
 ensures multiset(result[..]) == multiset(m_dataEntries[..])
{
  result := new T[m_dataEntries.Length];
  
  /* code modified by LLM (iteration 2): copy elements from input array to result array */
  var i := 0;
  while i < m_dataEntries.Length
    invariant 0 <= i <= m_dataEntries.Length
    invariant result.Length == m_dataEntries.Length
    invariant forall k :: 0 <= k < i ==> result[k] == m_dataEntries[k]
    /* code modified by LLM (iteration 2): strengthen multiset invariant to include remaining elements */
    invariant multiset(result[..i]) == multiset(m_dataEntries[..i])
    invariant forall k :: i <= k < result.Length ==> result[k] == result[0]
  {
    result[i] := m_dataEntries[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 2): add lemma call to establish multiset equality */
  assert result[..] == m_dataEntries[..];
  assert multiset(result[..]) == multiset(m_dataEntries[..]);
  
  /* code modified by LLM (iteration 2): Fisher-Yates shuffle with proper invariants */
  if m_dataEntries.Length > 1 {
    var j := m_dataEntries.Length - 1;
    while j > 0
      invariant 0 <= j < m_dataEntries.Length
      invariant result.Length == m_dataEntries.Length
      invariant multiset(result[..]) == multiset(m_dataEntries[..])
    {
      var randomIndex := random(0, j);
      /* code modified by LLM (iteration 2): added bounds check for random index */
      if 0 <= randomIndex <= j {
        swap(result, j, randomIndex);
      }
      j := j - 1;
    }
  }
}