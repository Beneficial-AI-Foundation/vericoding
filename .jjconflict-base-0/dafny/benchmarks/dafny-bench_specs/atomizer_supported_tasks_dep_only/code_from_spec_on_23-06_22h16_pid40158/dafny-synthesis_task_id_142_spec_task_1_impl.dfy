//IMPL 
/* code modified by LLM (iteration 4): Enhanced helper lemma with explicit set inclusion proofs */
lemma SetEqualityLemma(a: seq<int>, b: seq<int>, c: seq<int>, i: int)
    requires |a| == |b| && |b| == |c|
    requires i == |a|
    ensures (set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]) == 
            (set j: int | 0 <= j < |a| && a[j] == b[j] && b[j] == c[j])
{
    var loopSet := set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j];
    var postSet := set j: int | 0 <= j < |a| && a[j] == b[j] && b[j] == c[j];
    
    // Prove both directions of set equality
    assert forall j :: j in loopSet ==> j in postSet by {
        forall j | j in loopSet ensures j in postSet {
            assert 0 <= j < i && a[j] == b[j] && b[j] == c[j];
            assert i == |a|;
            assert 0 <= j < |a| && a[j] == b[j] && b[j] == c[j];
        }
    }
    
    assert forall j :: j in postSet ==> j in loopSet by {
        forall j | j in postSet ensures j in loopSet {
            assert 0 <= j < |a| && a[j] == b[j] && b[j] == c[j];
            assert i == |a|;
            assert 0 <= j < i && a[j] == b[j] && b[j] == c[j];
        }
    }
}

method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
    count := 0;
    var i := 0;
    
    while i < |a|
        invariant 0 <= i <= |a|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]|
    {
        if a[i] == b[i] && b[i] == c[i] {
            count := count + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Use enhanced helper lemma to prove postcondition */
    SetEqualityLemma(a, b, c, i);
}