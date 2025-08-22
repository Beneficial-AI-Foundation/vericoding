// ATOM 
predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// IMPL CountUppercase
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
    {
        /* code modified by LLM (iteration 1): Added set cardinality lemma to help Dafny verify the invariant */
        var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
        var newSet := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
        
        if IsUpperCase(s[i]) {
            /* code modified by LLM (iteration 1): Added assertion to show set relationship when character is uppercase */
            assert newSet == oldSet + {i};
            assert |newSet| == |oldSet| + 1;
            count := count + 1;
        } else {
            /* code modified by LLM (iteration 1): Added assertion to show set relationship when character is not uppercase */
            assert newSet == oldSet;
            assert |newSet| == |oldSet|;
        }
        i := i + 1;
    }
}