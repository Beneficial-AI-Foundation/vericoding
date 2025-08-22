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
        if IsUpperCase(s[i]) {
            /* code modified by LLM (iteration 2): Added lemma call to prove set cardinality increase */
            SetCardinalityLemma(s, i);
            count := count + 1;
        } else {
            /* code modified by LLM (iteration 2): Added lemma call to prove set cardinality stays same */
            SetCardinalityLemmaNoChange(s, i);
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 2): Added helper lemma for when uppercase character is found */
lemma SetCardinalityLemma(s: string, i: int)
    requires 0 <= i < |s|
    requires IsUpperCase(s[i])
    ensures | set j: int | 0 <= j < i+1 && IsUpperCase(s[j])| == | set j: int | 0 <= j < i && IsUpperCase(s[j])| + 1
{
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsUpperCase(s[j]);
    
    assert newSet == oldSet + {i};
    assert i !in oldSet;
}

/* code modified by LLM (iteration 2): Added helper lemma for when non-uppercase character is found */
lemma SetCardinalityLemmaNoChange(s: string, i: int)
    requires 0 <= i < |s|
    requires !IsUpperCase(s[i])
    ensures | set j: int | 0 <= j < i+1 && IsUpperCase(s[j])| == | set j: int | 0 <= j < i && IsUpperCase(s[j])|
{
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsUpperCase(s[j]);
    
    assert newSet == oldSet;
}