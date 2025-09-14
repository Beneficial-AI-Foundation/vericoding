method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma ProperSubsetImpliesExistsNonAvoidIndex<T>(m_workList: seq<T>, avoidSet: seq<T>)
  requires set_of_seq(avoidSet) < set_of_seq(m_workList)
  ensures exists i :: 0 <= i < |m_workList| && m_workList[i] !in avoidSet
{
  var s1 := set_of_seq(avoidSet);
  var s2 := set_of_seq(m_workList);
  var x :| x in s2 && x !in s1;
  var i :| 0 <= i < |m_workList| && m_workList[i] == x;
  if m_workList[i] in avoidSet {
    assert m_workList[i] == x;
    assert x in s1;
    assert x !in s1;
    assert false;
  }
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
  var i := 0;
  while i < m_workList.Length && m_workList[i] in avoidSet
    invariant 0 <= i <= m_workList.Length
    invariant forall k :: 0 <= k < i ==> m_workList[k] in avoidSet
  {
    i := i + 1;
  }
  if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
    ProperSubsetImpliesExistsNonAvoidIndex(m_workList[..], avoidSet);
  }
  if i < m_workList.Length {
    e := m_workList[i];
  } else {
    e := m_workList[0];
  }
}
// </vc-code>

