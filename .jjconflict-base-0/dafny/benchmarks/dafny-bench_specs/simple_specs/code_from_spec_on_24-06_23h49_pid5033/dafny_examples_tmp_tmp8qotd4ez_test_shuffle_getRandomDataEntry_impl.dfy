//ATOM

function set_of_seq<T>(s: seq<T>): set<T>
{
 set x: T | x in s :: x
}


//ATOM

method random(a: int, b: int) returns (r: int)
 requires a <= b
 ensures a <= r <= b
{
}


//IMPL getRandomDataEntry

method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
 requires m_workList.Length > 0
 ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
 ensures avoidSet < m_workList[..] ==> e in m_workList[..]
{
    /* code modified by LLM (iteration 1): Fixed logic and added proper verification support */
    var avoidSetAsSet := set_of_seq(avoidSet);
    var workListAsSet := set_of_seq(m_workList[..]);
    
    // Check if we need to avoid elements in avoidSet (first postcondition)
    if avoidSetAsSet < workListAsSet {
        // Must find an element not in avoidSet
        var i := 0;
        while i < m_workList.Length
            invariant 0 <= i <= m_workList.Length
            invariant avoidSetAsSet < workListAsSet
            invariant forall j :: 0 <= j < i ==> m_workList[j] in avoidSet
        {
            if m_workList[i] !in avoidSet {
                e := m_workList[i];
                /* code modified by LLM (iteration 1): Added verification assertions */
                assert e == m_workList[i];
                assert e in m_workList[..];
                assert e !in avoidSet;
                return;
            }
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 1): Added proof that this case is impossible */
        // If we reach here, all elements in m_workList are in avoidSet
        // This contradicts avoidSetAsSet < workListAsSet
        assert forall j :: 0 <= j < m_workList.Length ==> m_workList[j] in avoidSet;
        assert workListAsSet <= avoidSetAsSet;
        assert false; // Contradiction
        
        // Unreachable, but needed for definite assignment
        e := m_workList[0];
    } else {
        /* code modified by LLM (iteration 1): Handle case where avoidSet constraint doesn't apply */
        // Pick any element from workList
        var index := random(0, m_workList.Length - 1);
        e := m_workList[index];
        
        /* code modified by LLM (iteration 1): Verification assertion */
        assert 0 <= index < m_workList.Length;
        assert e in m_workList[..];
    }
}