
// SPEC 

method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b
// ATOM 

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures t in s1 <==> t in s2
{
  calc <==> {
    t in s1;
    t in multiset(s1);
    // Not necessary:
//    t in multiset(s2);
//    t in s2;
  }
/*  
  if (t in s1) {
  }
  else {
  }
*/
}


// ATOM 

lemma eqMultiset<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures forall t :: t in s1 <==> t in s2
{
  forall t {
    eqMultiset_t(t, s1, s2);
  }
}


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

  
// SPEC 
  
method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
  // requires m_dataEntries != null
  // ensures result != null
  ensures result.Length == m_dataEntries.Length
  ensures multiset(result[..]) == multiset(m_dataEntries[..])
{
}


// ATOM 

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}


// ATOM 

lemma in_set_of_seq<T>(x: T, s: seq<T>)
  ensures x in s <==> x in set_of_seq(s)
// ATOM 

lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  requires set_of_seq(s1) <= set_of_seq(s2)
  ensures forall x :: x in s1 ==> x in s2
// SPEC 
  
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
//  ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
//  ensures avoidSet < m_workList[..] ==> e in m_workList[..]
{
}




