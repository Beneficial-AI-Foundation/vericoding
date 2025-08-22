//IMPL 
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    /* code modified by LLM (iteration 4): Added edge case handling for empty subsequence */
    if |sub| == 0 {
        result := true;
        return;
    }
    
    /* code modified by LLM (iteration 4): Added edge case handling when sub is longer than main */
    if |sub| > |main| {
        result := false;
        return;
    }
    
    var i := 0;
    /* code modified by LLM (iteration 4): Fixed loop invariants to properly track search progress */
    while i <= |main| - |sub|
        invariant 0 <= i <= |main| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> sub != main[j..j + |sub|]
        invariant |sub| <= |main|
    {
        if sub == main[i..i + |sub|] {
            /* code modified by LLM (iteration 4): Added assertion to help verify postcondition when match found */
            assert 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|];
            result := true;
            return;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help verify postcondition when no match found */
    assert i == |main| - |sub| + 1;
    assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|];
    result := false;
}