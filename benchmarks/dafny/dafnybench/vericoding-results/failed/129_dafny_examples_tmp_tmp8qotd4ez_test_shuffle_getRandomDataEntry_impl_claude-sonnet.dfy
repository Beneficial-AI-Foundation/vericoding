method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma proper_subset_exists<T>(s1: set<T>, s2: set<T>)
  requires s1 < s2
  ensures exists x :: x in s2 && x !in s1
{
}

lemma seq_to_set_membership<T>(s: seq<T>, x: T)
  ensures x in s ==> x in set_of_seq(s)
  ensures x in set_of_seq(s) ==> x in s
{
}

lemma array_element_in_set<T>(arr: array<T>, i: int)
  requires 0 <= i < arr.Length
  ensures arr[i] in set_of_seq(arr[..])
{
  assert arr[i] == arr[..][i];
  assert arr[i] in arr[..];
}

lemma proper_subset_guarantees_element<T>(avoidSet: seq<T>, m_workList: array<T>)
  requires set_of_seq(avoidSet) < set_of_seq(m_workList[..])
  requires m_workList.Length > 0
  ensures exists i :: 0 <= i < m_workList.Length && m_workList[i] !in avoidSet
{
  proper_subset_exists(set_of_seq(avoidSet), set_of_seq(m_workList[..]));
  assert exists x :: x in set_of_seq(m_workList[..]) && x !in set_of_seq(avoidSet);
  var x :| x in set_of_seq(m_workList[..]) && x !in set_of_seq(avoidSet);
  seq_to_set_membership(m_workList[..], x);
  assert x in m_workList[..];
  seq_to_set_membership(avoidSet, x);
  assert x !in avoidSet;
  var i :| 0 <= i < m_workList.Length && m_workList[..][i] == x;
  assert m_workList[i] == x;
}

lemma avoid_set_element_membership<T>(avoidSet: seq<T>, x: T)
  ensures x in avoidSet ==> x in set_of_seq(avoidSet)
  ensures x !in avoidSet ==> x !in set_of_seq(avoidSet)
{
  seq_to_set_membership(avoidSet, x);
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
  if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
    proper_subset_guarantees_element(avoidSet, m_workList);
    var i := 0;
    while i < m_workList.Length
      invariant 0 <= i <= m_workList.Length
      invariant exists j :: i <= j < m_workList.Length && m_workList[j] !in avoidSet
    {
      if m_workList[i] !in avoidSet {
        array_element_in_set(m_workList, i);
        avoid_set_element_membership(avoidSet, m_workList[i]);
        return m_workList[i];
      }
      i := i + 1;
    }
    assert false;
  } else {
    array_element_in_set(m_workList, 0);
    return m_workList[0];
  }
}
// </vc-code>

