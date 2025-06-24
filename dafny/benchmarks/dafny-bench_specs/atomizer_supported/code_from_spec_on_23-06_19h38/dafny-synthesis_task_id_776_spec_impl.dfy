// ATOM 
predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

//IMPL CountVowelNeighbors
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count >= 0
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            /* code modified by LLM (iteration 3): Added assertion to help Dafny prove set cardinality increment */
            var oldSet := set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]);
            var newSet := set j: int | 1 <= j < i+1 && IsVowel(s[j-1]) && IsVowel(s[j+1]);
            assert newSet == oldSet + {i};
            assert i !in oldSet;
            assert |newSet| == |oldSet| + 1;
            count := count + 1;
        }
        i := i + 1;
    }
}