// IMPL 

method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
{
  /* code modified by LLM (iteration 1): Fixed logic to handle case when a > b correctly */
  if a <= b {
    r := a;
  } else {
    r := 0;  // This satisfies the postcondition since when a > b, the implication is vacuously true
  }
}

//ATOM eqMultiset_t
predicate eqMultiset_t<T>(a: array<T>, b: array<T>)
  reads a, b
{
  a.Length == b.Length && multiset(a[..]) == multiset(b[..])
}

//ATOM eqMultiset
predicate eqMultiset<T>(s1: seq<T>, s2: seq<T>)
{
  multiset(s1) == multiset(s2)
}

// IMPL 

method swap<T>(a: array<T>, i: int, j: int)
  // requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  /* code modified by LLM (iteration 1): Added conditional check to handle case when i == j */
  if i == j {
    // No swap needed, postconditions are trivially satisfied
  } else {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
  }
}

  
// IMPL 
  
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
    /* code modified by LLM (iteration 1): Added proper loop invariant to maintain multiset equality */
    invariant forall k :: 0 <= k < i ==> result[k] == m_dataEntries[k]
    invariant multiset(result[..i]) == multiset(m_dataEntries[..i])
  {
    result[i] := m_dataEntries[i];
    i := i + 1;
  }
}

//ATOM set_of_seq
function set_of_seq<T>(s: seq<T>): set<T>
{
  set x | x in s
}

//ATOM in_set_of_seq
lemma in_set_of_seq<T>(s: seq<T>, x: T)
  ensures x in s ==> x in set_of_seq(s)
  ensures x in set_of_seq(s) ==> x in s
{
}

//ATOM subset_set_of_seq
lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  requires forall x :: x in s1 ==> x in s2
  ensures set_of_seq(s1) <= set_of_seq(s2)
{
}

//ATOM getRandomDataEntry
method getRandomDataEntry<T>(entries: array<T>) returns (entry: T)
  requires entries.Length > 0
  ensures entry in entries[..]
{
  var idx := 0;
  entry := entries[idx];
}