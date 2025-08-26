predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
// Helper lemma to establish set equality for the loop invariant
lemma SetUpdateLemma(s: string, i: int, oldCount: int, newCount: int)
    requires 1 <= i < |s| - 1
    requires oldCount == |set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])|
    requires newCount == oldCount + (if IsVowel(s[i-1]) && IsVowel(s[i+1]) then 1 else 0)
    ensures newCount == |set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1])|
{
    var oldSet := set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    var newSet := set j: int | 1 <= j < i + 1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
    
    if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
        assert newSet == oldSet + {i};
        assert i !in oldSet;
        assert |newSet| == |oldSet| + 1;
    } else {
        assert newSet == oldSet;
        assert |newSet| == |oldSet|;
    }
}
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
    count := 0;
    
    if |s| <= 2 {
        return;
    }
    
    var i := 1;
    
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count >= 0
        invariant count == | set j: int {:trigger IsVowel(s[j-1]), IsVowel(s[j+1])} | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    {
        var oldCount := count;
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        SetUpdateLemma(s, i, oldCount, count);
        i := i + 1;
    }
}
// </vc-code>