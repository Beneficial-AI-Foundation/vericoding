method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma strict_subset_implies_exists<T>(avoidSet: seq<T>, workList: seq<T>)
  requires set_of_seq(avoidSet) < set_of_seq(workList)
  ensures exists x :: x in workList && x !in avoidSet
{
  var avoidSetSet := set_of_seq(avoidSet);
  var workListSet := set_of_seq(workList);
  
  if forall x :: x in workList ==> x in avoidSet {
    assert forall x :: x in workListSet ==> x in avoidSetSet;
    assert workListSet <= avoidSetSet;
    assert false; // Contradiction with strict subset
  }
}

lemma all_in_avoid_contradicts_strict_subset<T>(avoidSet: seq<T>, workList: seq<T>)
  requires forall x :: x in workList ==> x in avoidSet
  ensures !(set_of_seq(avoidSet) < set_of_seq(workList))
{
  var avoidSetSet := set_of_seq(avoidSet);
  var workListSet := set_of_seq(workList);
  
  assert forall x :: x in workListSet ==> x in avoidSetSet;
  assert workListSet <= avoidSetSet;
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
  while i < m_workList.Length
    invariant 0 <= i <= m_workList.Length
    invariant forall j :: 0 <= j < i ==> m_workList[j] in avoidSet
    invariant set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> 
              exists j :: i <= j < m_workList.Length && m_workList[j] !in avoidSet
  {
    if m_workList[i] !in avoidSet {
      e := m_workList[i];
      return;
    }
    i := i + 1;
  }
  // If we reach here, all elements are in avoidSet
  // This means set_of_seq(avoidSet) >= set_of_seq(m_workList[..])
  // So the precondition set_of_seq(avoidSet) < set_of_seq(m_workList[..]) is false
  assert forall j :: 0 <= j < m_workList.Length ==> m_workList[j] in avoidSet;
  assert forall x :: x in m_workList[..] ==> x in avoidSet;
  all_in_avoid_contradicts_strict_subset(avoidSet, m_workList[..]);
  assert !(set_of_seq(avoidSet) < set_of_seq(m_workList[..]));
  e := m_workList[0];
}
// </vc-code>

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
    assert t in multiset(s1);
  }
  else {
    assert t !in multiset(s1);
  }
*/
}

lemma eqMultiset<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures forall t :: t in s1 <==> t in s2
{
  forall t {
    eqMultiset_t(t, s1, s2);
  }
}

lemma in_set_of_seq<T>(x: T, s: seq<T>)
  ensures x in s <==> x in set_of_seq(s)

lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  requires set_of_seq(s1) <= set_of_seq(s2)
  ensures forall x :: x in s1 ==> x in s2