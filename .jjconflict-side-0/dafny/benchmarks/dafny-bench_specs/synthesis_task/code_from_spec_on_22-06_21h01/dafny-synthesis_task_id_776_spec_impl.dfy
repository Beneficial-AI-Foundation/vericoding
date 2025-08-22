// ATOM
predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

// IMPL CountVowelNeighbors
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count >= 0
        /* code modified by LLM (iteration 4): Fixed loop invariant to count elements from 1 up to but not including i */
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): When loop exits, i == |s| - 1, so we have counted all elements in range [1, |s|-1) */
    assert i == |s| - 1;
    assert count == | set j: int | 1 <= j < |s|-1 && IsVowel(s[j-1]) && IsVowel(s[j+1]) |;
}