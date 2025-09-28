// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove empty subsequence property */
lemma EmptySubseqLemma(sub: seq<int>, main: seq<int>)
    ensures |sub| == 0 ==> exists i :: IsSubseqAt(sub, main, i)
{
    if |sub| == 0 {
        assert IsSubseqAt(sub, main, 0);
    }
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added lemma call to prove empty subsequence case */
    EmptySubseqLemma(sub, main);
    
    if |sub| == 0 {
        result := true;
        return;
    }
    if |sub| > |main| {
        result := false;
        return;
    }
    
    var i := 0;
    while i <= |main| - |sub|
        invariant 0 <= i <= |main| - |sub| + 1
        invariant forall k :: 0 <= k < i ==> !IsSubseqAt(sub, main, k)
    {
        var matches := true;
        var j := 0;
        while j < |sub| && matches
            invariant 0 <= j <= |sub|
            invariant matches <==> (forall k :: 0 <= k < j ==> sub[k] == main[i + k])
        {
            if sub[j] != main[i + j] {
                matches := false;
            }
            j := j + 1;
        }
        
        if matches {
            assert IsSubseqAt(sub, main, i);
            result := true;
            return;
        }
        
        i := i + 1;
    }
    
    result := false;
}
// </vc-code>
