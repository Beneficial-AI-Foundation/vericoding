method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma lemma_set_subset_property<T>(s: seq<T>, avoid: set<T>)
  ensures set_of_seq(s) <= avoid ==> (forall x :: x in s ==> x in avoid)
{
}

lemma lemma_not_in_avoid<T>(s: seq<T>, avoid: set<T>, e: T)
  requires set_of_seq(s) <= avoid
  requires e in s
  ensures e in avoid
{
}

lemma lemma_subset_transitive<T>(s1: set<T>, s2: set<T>, s3: set<T>)
  requires s1 <= s2 && s2 <= s3
  ensures s1 <= s3
{
}

lemma lemma_element_in_set<T>(e: T, s: seq<T>)
  requires e in s
  ensures e in set_of_seq(s)
{
}

lemma lemma_set_eq_property<T>(s: seq<T>)
  ensures set_of_seq(s) == set x | x in s
{
}

lemma lemma_strict_subset_implies_not_all_elements<T>(s1: set<T>, s2: set<T>)
  requires s1 < s2
  ensures exists x :: x in s2 && x !in s1
{
}

lemma lemma_array_element_in_slice<T>(arr: array<T>, index: int)
  requires 0 <= index < arr.Length
  ensures arr[index] in arr[..]
{
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
  var index : int;
  index := random(0, m_workList.Length - 1);
  e := m_workList[index];
  
  lemma_array_element_in_slice(m_workList, index);
  
  if (set_of_seq(avoidSet) < set_of_seq(m_workList[..])) {
    lemma_element_in_set(e, m_workList[..]);
    assert e in set_of_seq(m_workList[..]);
    lemma_strict_subset_implies_not_all_elements(set_of_seq(avoidSet), set_of_seq(m_workList[..]));
    assert exists x :: x in set_of_seq(m_workList[..]) && x !in set_of_seq(avoidSet);
    assert e !in set_of_seq(avoidSet);
  }
}
// </vc-code>

