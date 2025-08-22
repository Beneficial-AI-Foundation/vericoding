// ATOM 
predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// IMPL 
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var i := 1;
    while i < |s| - 1
        /* code modified by LLM (iteration 4): fixed loop invariant bounds and added decreases clause */
        invariant 1 <= i <= |s| - 1
        invariant count >= 0
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
        decreases |s| - 1 - i
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): added assertion to help Dafny verify the postcondition */
    assert i == |s| - 1;
    assert count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |;
    assert (set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1])) == (set j: int | 1 <= j < |s|-1 && IsVowel(s[j-1]) && IsVowel(s[j+1]));
}