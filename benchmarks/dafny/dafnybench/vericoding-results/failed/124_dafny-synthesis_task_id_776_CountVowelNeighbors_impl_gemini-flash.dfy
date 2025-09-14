predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
    var numVowelNeighbors := 0;
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant numVowelNeighbors == | set k: int | 1 <= k < i && IsVowel(s[k-1]) && IsVowel(s[k+1]) |
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            numVowelNeighbors := numVowelNeighbors + 1;
        }
        i := i + 1;
    }
    return numVowelNeighbors;
}
// </vc-code>

