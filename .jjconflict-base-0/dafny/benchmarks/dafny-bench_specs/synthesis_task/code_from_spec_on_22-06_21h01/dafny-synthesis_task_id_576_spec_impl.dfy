//IMPL 
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    /* code modified by LLM (iteration 4): Fixed edge case handling for when sub is larger than main */
    if |sub| > |main| {
        result := false;
        return;
    }
    
    /* code modified by LLM (iteration 4): Added edge case handling for empty subsequence */
    if |sub| == 0 {
        result := true;
        return;
    }
    
    var i := 0;
    /* code modified by LLM (iteration 4): Fixed loop invariants to properly establish postcondition */
    while i <= |main| - |sub|
        invariant 0 <= i
        invariant |sub| <= |main|
        invariant |sub| > 0
        invariant forall j :: 0 <= j < i ==> sub != main[j..j + |sub|]
        invariant i <= |main| - |sub| + 1
    {
        if sub == main[i..i + |sub|] {
            result := true;
            return;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help establish the postcondition */
    assert i == |main| - |sub| + 1;
    assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|];
    result := false;
}