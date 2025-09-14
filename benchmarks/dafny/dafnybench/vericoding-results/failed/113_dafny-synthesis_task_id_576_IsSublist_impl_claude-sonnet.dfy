

// <vc-helpers>
lemma SublistExists(sub: seq<int>, main: seq<int>, i: int)
    requires 0 <= i <= |main| - |sub|
    requires sub == main[i..i + |sub|]
    ensures exists j {:trigger main[j..j + |sub|]} :: 0 <= j <= |main| - |sub| && sub == main[j..j + |sub|]
{
}

lemma SublistMatches(sub: seq<int>, main: seq<int>, i: int)
    requires 0 <= i <= |main| - |sub|
    requires forall k :: 0 <= k < |sub| ==> sub[k] == main[i + k]
    ensures sub == main[i..i + |sub|]
{
    if |sub| == 0 {
        assert sub == main[i..i];
    } else {
        assert sub == main[i..i + |sub|];
    }
}

lemma LoopInvariantMaintained(sub: seq<int>, main: seq<int>, i: int)
    requires 0 <= i <= |main| - |sub|
    requires forall j {:trigger main[j..j + |sub|]} :: 0 <= j < i ==> sub != main[j..j + |sub|]
    requires sub != main[i..i + |sub|]
    ensures forall j {:trigger main[j..j + |sub|]} :: 0 <= j < i + 1 ==> sub != main[j..j + |sub|]
{
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
    if |sub| > |main| {
        return false;
    }
    
    var i := 0;
    while i <= |main| - |sub|
        invariant 0 <= i <= |main| - |sub| + 1
        invariant forall j {:trigger main[j..j + |sub|]} :: 0 <= j < i ==> sub != main[j..j + |sub|]
    {
        var isMatch := true;
        var k := 0;
        while k < |sub| && isMatch
            invariant 0 <= k <= |sub|
            invariant isMatch <==> forall m :: 0 <= m < k ==> sub[m] == main[i + m]
        {
            if sub[k] != main[i + k] {
                isMatch := false;
            }
            k := k + 1;
        }
        
        if isMatch {
            SublistMatches(sub, main, i);
            SublistExists(sub, main, i);
            return true;
        }
        
        assert sub != main[i..i + |sub|];
        LoopInvariantMaintained(sub, main, i);
        i := i + 1;
    }
    
    return false;
}
// </vc-code>

