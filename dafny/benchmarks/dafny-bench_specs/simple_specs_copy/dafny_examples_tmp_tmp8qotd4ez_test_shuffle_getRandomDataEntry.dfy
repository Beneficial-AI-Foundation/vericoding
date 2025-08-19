//ATOM

function set_of_seq<T>(s: seq<T>): set<T>
{
 set x: T | x in s :: x
}


//ATOM

method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b


// SPEC
 
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
 requires m_workList.Length > 0
// ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
// ensures avoidSet < m_workList[..] ==> e in m_workList[..]
{
}
