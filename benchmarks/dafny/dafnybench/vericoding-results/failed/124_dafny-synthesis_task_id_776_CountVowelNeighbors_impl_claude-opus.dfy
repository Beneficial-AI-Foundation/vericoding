predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
ghost function VowelNeighborSet(s: string, k: int): set<int>
{
    set i: int {:trigger i in VowelNeighborSet(s, k)} | 1 <= i < k && i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1])
}

lemma VowelNeighborSetExtend(s: string, k: int)
    requires 1 <= k < |s|-1
    ensures VowelNeighborSet(s, k+1) == 
        if IsVowel(s[k-1]) && IsVowel(s[k+1]) then 
            VowelNeighborSet(s, k) + {k}
        else 
            VowelNeighborSet(s, k)
{
    if IsVowel(s[k-1]) && IsVowel(s[k+1]) {
        assert VowelNeighborSet(s, k+1) == VowelNeighborSet(s, k) + {k};
    } else {
        assert k !in VowelNeighborSet(s, k+1);
        assert VowelNeighborSet(s, k+1) == VowelNeighborSet(s, k);
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
        assert (set i: int {:trigger IsVowel(s[i-1])} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1])) == {};
        return count;
    }
    
    var i := 1;
    ghost var seen := {};
    
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant seen == VowelNeighborSet(s, i)
        invariant count == |seen|
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
            seen := seen + {i};
        }
        VowelNeighborSetExtend(s, i);
        i := i + 1;
    }
    
    assert seen == (set i: int {:trigger IsVowel(s[i-1])} | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]));
}
// </vc-code>

