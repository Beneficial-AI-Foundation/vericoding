method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma SetOfSeqSubset<T>(s1: seq<T>, s2: seq<T>)
  requires s1 < s2
  ensures set_of_seq(s1) <= set_of_seq(s2)
{
  // This follows from the definition of subsequence and set_of_seq
}

lemma ExistsNotInAvoidSet<T(==)>(m_workList: array<T>, avoidSet: seq<T>)
  requires m_workList.Length > 0
  requires set_of_seq(avoidSet) < set_of_seq(m_workList[..])
  ensures exists i :: 0 <= i < m_workList.Length && m_workList[i] !in avoidSet
{
  // Since set_of_seq(avoidSet) is a proper subset of set_of_seq(m_workList[..]),
  // there must be at least one element in m_workList that's not in avoidSet
  var witness: T :| witness in set_of_seq(m_workList[..]) && witness !in set_of_seq(avoidSet);
  assert witness in m_workList[..];
  var i: int :| 0 <= i < m_workList.Length && m_workList[i] == witness;
  assert m_workList[i] !in avoidSet;
}
// </vc-helpers>

// <vc-spec>
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
  ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
  ensures avoidSet < m_workList[..] ==> e in m_workList[..]
// </vc-spec>
// <vc-code>
{
  var index := random(0, m_workList.Length - 1);
  e := m_workList[index];
  
  if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
    // Try to find an element not in avoidSet
    ExistsNotInAvoidSet(m_workList, avoidSet);
    while e in avoidSet
      invariant 0 <= index < m_workList.Length
      invariant e == m_workList[index]
      decreases m_workList.Length - index
    {
      if index < m_workList.Length - 1 {
        index := index + 1;
      } else {
        index := 0;
      }
      e := m_workList[index];
    }
  }
}
// </vc-code>

