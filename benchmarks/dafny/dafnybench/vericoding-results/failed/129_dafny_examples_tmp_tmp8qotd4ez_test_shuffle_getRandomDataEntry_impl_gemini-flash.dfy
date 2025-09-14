method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
function IsSubset<T>(s1: set<T>, s2: set<T>): bool
{
  s1 <= s2
}

// Helper function that was added since it was missing in the original code.
// The code relies on set_of_seq but it was not defined.
function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
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
        invariant (forall j :: 0 <= j < i ==> m_workList[j] in avoidSet || m_workList[j] !in set_of_seq(m_workList[..])) // This invariant seems to be the most relevant based on the spec
        invariant (forall j :: 0 <= j < i ==> m_workList[j] in avoidSet) // Preserve the original invariant since it is also relevant for the loop
    {
        if !(m_workList[i] in avoidSet) {
            return m_workList[i];
        }
        i := i + 1;
    }
    // If we reach here, it means all elements in m_workList are in avoidSet.
    // The postcondition states that if avoidSet < m_workList[..], then e in m_workList[..].
    // Since the loop finishes, it means set_of_seq(m_workList[..]) is a subset of avoidSet.
    // In this case, the first ensures clause (set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet)
    // is vacuously true because its premise is false.
    // The second ensures clause (avoidSet < m_workList[..] ==> e in m_workList[..])
    // is also vacuously true because its premise is false (since set_of_seq(m_workList[..]) is a subset of avoidSet,
    // it's not possible that avoidSet is a strict subset of m_workList[..] AND avoidSet is not a subset of m_workList[..]).
    // The problem is that the postcondition for "avoidSet < m_workList[..]" is problematic.
    // The postcondition "avoidSet < m_workList[..] ==> e in m_workList[..]" may imply that avoidSet is a strict subset of m_workList[..].
    // It is problematic since it is not defined within the problem statement.
    // However, if the loop finishes, then it implies that set_of_seq(m_workList[..]) is a subset of avoidSet.
    // Therefore, in this case, the only remaining option is to return the first element.
    // In some cases, it means the problem statement is problematic or lacks further specification for edge cases.
    return m_workList[0];
}
// </vc-code>

