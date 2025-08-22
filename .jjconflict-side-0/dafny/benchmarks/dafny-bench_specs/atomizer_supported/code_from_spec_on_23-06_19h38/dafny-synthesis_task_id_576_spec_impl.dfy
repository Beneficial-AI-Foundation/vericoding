//IMPL 
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    /* code modified by LLM (iteration 4): Handle empty subsequence case explicitly */
    if |sub| == 0 {
        result := true;
        return;
    }
    
    /* code modified by LLM (iteration 4): Handle case where sub is longer than main */
    if |sub| > |main| {
        result := false;
        return;
    }
    
    var i := 0;
    /* code modified by LLM (iteration 4): Fixed loop bounds and invariants with proper range handling */
    while i <= |main| - |sub|
        invariant 0 <= i <= |main| - |sub| + 1
        invariant |sub| > 0
        invariant |sub| <= |main|
        invariant forall j :: 0 <= j < i && j <= |main| - |sub| ==> sub != main[j..j + |sub|]
        decreases |main| - |sub| + 1 - i
    {
        if sub == main[i..i + |sub|] {
            /* code modified by LLM (iteration 4): Added assertion to establish postcondition when match found */
            assert sub == main[i..i + |sub|] && 0 <= i <= |main| - |sub|;
            result := true;
            return;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertions to establish postcondition when no match found */
    assert i == |main| - |sub| + 1;
    assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|];
    result := false;
}