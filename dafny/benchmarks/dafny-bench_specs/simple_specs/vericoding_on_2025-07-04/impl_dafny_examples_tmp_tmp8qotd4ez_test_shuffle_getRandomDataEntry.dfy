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


//IMPL

method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
 requires m_workList.Length > 0
 ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
 ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e in m_workList[..]
{
    /* code modified by LLM (iteration 3): Added helper lemma for existence proof */
    lemma ExistenceHelper(arr: array<T>, avoid: seq<T>)
        requires set_of_seq(avoid) < set_of_seq(arr[..])
        ensures exists k :: 0 <= k < arr.Length && arr[k] !in avoid
    {
        var arrSet := set_of_seq(arr[..]);
        var avoidSet := set_of_seq(avoid);
        assert avoidSet < arrSet;
        assert exists x :: x in arrSet && x !in avoidSet;
        var witness :| witness in arrSet && witness !in avoidSet;
        assert witness in arr[..];
        var idx :| 0 <= idx < arr.Length && arr[idx] == witness;
        assert arr[idx] !in avoid;
    }

    /* code modified by LLM (iteration 3): Simplified approach with proper existence proof */
    var index := random(0, m_workList.Length - 1);
    e := m_workList[index];
    
    // If we need to avoid elements in avoidSet and there exists an element not in avoidSet
    if e in avoidSet && set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
        /* code modified by LLM (iteration 3): Call helper lemma to establish existence */
        ExistenceHelper(m_workList, avoidSet);
        
        var i := 0;
        while i < m_workList.Length && m_workList[i] in avoidSet
            invariant 0 <= i <= m_workList.Length
            invariant forall j :: 0 <= j < i ==> m_workList[j] in avoidSet
            invariant set_of_seq(avoidSet) < set_of_seq(m_workList[..])
            invariant exists k :: 0 <= k < m_workList.Length && m_workList[k] !in avoidSet
            decreases m_workList.Length - i
        {
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 3): Loop termination guaranteed by invariants */
        assert i < m_workList.Length;
        assert m_workList[i] !in avoidSet;
        e := m_workList[i];
    }
}