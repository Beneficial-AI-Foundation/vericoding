//IMPL random
method random(a: int, b: int) returns (r: int)
  requires a <= b
  ensures a <= b ==> a <= r <= b
{
  /* code modified by LLM (iteration 1): simplified logic since precondition guarantees a <= b */
  r := a;
}

//ATOM set_of_seq
function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

//IMPL getRandomDataEntry
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
  ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
  ensures avoidSet < m_workList[..] ==> e in m_workList[..]
{
  /* code modified by LLM (iteration 1): added proper initialization and logic to satisfy postconditions */
  e := m_workList[0];
  
  if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
    var i := 0;
    while i < m_workList.Length
      invariant 0 <= i <= m_workList.Length
      invariant e in m_workList[..]
      invariant forall j :: 0 <= j < i ==> m_workList[j] in avoidSet
    {
      if m_workList[i] !in avoidSet {
        e := m_workList[i];
        return;
      }
      i := i + 1;
    }
  }
  
  /* code modified by LLM (iteration 1): handle case when avoidSet < m_workList[..] */
  if avoidSet < m_workList[..] {
    var found := false;
    var i := 0;
    while i < m_workList.Length && !found
      invariant 0 <= i <= m_workList.Length
      invariant e in m_workList[..]
    {
      if m_workList[i] !in avoidSet {
        e := m_workList[i];
        found := true;
      }
      i := i + 1;
    }
  }
}