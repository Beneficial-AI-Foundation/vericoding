// Helper predicate to check if a character is uppercase
predicate IsUpperCase(c: char) {
    'A' <= c <= 'Z'
}

lemma SetCardinalityLemma(s: string, i: int)
    requires 0 <= i < |s|
    ensures var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
            var newSet := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
            if IsUpperCase(s[i]) then |newSet| == |oldSet| + 1
            else |newSet| == |oldSet|
{
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i + 1 && IsUpperCase(s[j]);
    
    if IsUpperCase(s[i]) {
        assert newSet == oldSet + {i};
        assert i !in oldSet;
    } else {
        assert newSet == oldSet;
    }
}

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
    {
        SetCardinalityLemma(s, i);
        if IsUpperCase(s[i]) {
            count := count + 1;
        }
        i := i + 1;
    }
}
// </vc-code>