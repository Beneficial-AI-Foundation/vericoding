//ATOM_PLACEHOLDER_fillK


//IMPL containsSubString
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
    ensures pos == -1 ==> (forall k :: 0 <= k <= a.Length - b.Length ==> (exists j :: 0 <= j < b.Length && a[k + j] != b[j]))
    ensures pos >= 0 ==> 0 <= pos <= a.Length - b.Length && (forall j :: 0 <= j < b.Length ==> a[pos + j] == b[j])
    ensures b.Length == 0 ==> pos == 0
{
    if b.Length == 0 {
        pos := 0;
        return;
    }
    
    var i := 0;
    /* code modified by LLM (iteration 4): fixed loop bounds to handle edge case properly */
    while i <= a.Length - b.Length
        invariant 0 <= i <= a.Length - b.Length + 1
        invariant forall k :: 0 <= k < i ==> (exists j :: 0 <= j < b.Length && a[k + j] != b[j])
        decreases a.Length - b.Length + 1 - i
    {
        var j := 0;
        var match := true;
        /* code modified by LLM (iteration 4): refined inner loop with corrected invariants */
        while j < b.Length && match
            invariant 0 <= j <= b.Length
            invariant match ==> (forall k :: 0 <= k < j ==> a[i + k] == b[k])
            invariant !match ==> (exists k :: 0 <= k < j && a[i + k] != b[k])
            invariant i <= a.Length - b.Length
            decreases b.Length - j
        {
            if a[i + j] != b[j] {
                match := false;
            } else {
                j := j + 1;
            }
        }
        if match {
            /* code modified by LLM (iteration 4): strengthened match verification */
            assert j == b.Length;
            assert forall k :: 0 <= k < b.Length ==> a[i + k] == b[k];
            pos := i;
            return;
        }
        /* code modified by LLM (iteration 4): added assertion to help with loop invariant */
        assert !match;
        assert exists k :: 0 <= k < b.Length && a[i + k] != b[k];
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): added comprehensive verification for not-found case */
    assert i == a.Length - b.Length + 1;
    assert forall k :: 0 <= k < i ==> (exists j :: 0 <= j < b.Length && a[k + j] != b[j]);
    assert forall k :: 0 <= k <= a.Length - b.Length ==> 0 <= k < i;
    pos := -1;
}