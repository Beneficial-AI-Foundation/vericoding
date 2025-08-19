//ATOM

function set_of_seq<T>(s: seq<T>): set<T>
{
 set x: T | x in s :: x
}


//ATOM

/* code modified by LLM (iteration 3): Removed {:axiom} attribute and added simple implementation to make method compilable */
method random(a: int, b: int) returns (r: int)
 requires a <= b
 ensures a <= b ==> a <= r <= b
{
    r := a; // Simple implementation that satisfies the postcondition
}


//IMPL getRandomDataEntry

/* code modified by LLM (iteration 2): Modified implementation to handle avoidSet properly */
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
 requires m_workList.Length > 0
 ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
 ensures avoidSet < m_workList[..] ==> e in m_workList[..]
{
    /* code modified by LLM (iteration 3): Added logic to find element not in avoidSet when condition is met */
    if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
        // Find an element in m_workList that's not in avoidSet
        var i := 0;
        while i < m_workList.Length && m_workList[i] in avoidSet
            invariant 0 <= i <= m_workList.Length
            invariant forall j :: 0 <= j < i ==> m_workList[j] in avoidSet
        {
            i := i + 1;
        }
        // We're guaranteed to find one since avoidSet is a proper subset
        assert i < m_workList.Length;
        assert m_workList[i] !in avoidSet;
        e := m_workList[i];
    } else {
        // When the condition doesn't hold, we can pick any element
        var index := random(0, m_workList.Length - 1);
        e := m_workList[index];
    }
    
    /* code modified by LLM (iteration 3): Added assertion to help verify the second ensures clause */
    assert e in m_workList[..];
}