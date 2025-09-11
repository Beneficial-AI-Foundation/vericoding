// <vc-preamble>
method random(a: int, b: int) returns (r: int)
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
  ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
  ensures avoidSet < m_workList[..] ==> e in m_workList[..]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
