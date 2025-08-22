// ATOM 
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// IMPL CountDigits
/* code modified by LLM (iteration 2): Added helper lemma to prove set cardinality when adding digit */
lemma SetCardinalityAddDigit(s: string, i: int)
    requires 0 <= i < |s|
    requires IsDigit(s[i])
    ensures | set j: int | 0 <= j < i+1 && IsDigit(s[j])| == | set j: int | 0 <= j < i && IsDigit(s[j])| + 1
{
    var oldSet := set j: int | 0 <= j < i && IsDigit(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsDigit(s[j]);
    
    assert newSet == oldSet + {i};
    assert i !in oldSet;
}

/* code modified by LLM (iteration 2): Added helper lemma to prove set cardinality when adding non-digit */
lemma SetCardinalityAddNonDigit(s: string, i: int)
    requires 0 <= i < |s|
    requires !IsDigit(s[i])
    ensures | set j: int | 0 <= j < i+1 && IsDigit(s[j])| == | set j: int | 0 <= j < i && IsDigit(s[j])|
{
    var oldSet := set j: int | 0 <= j < i && IsDigit(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsDigit(s[j]);
    
    assert newSet == oldSet;
}

method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && IsDigit(s[j])|
    {
        if IsDigit(s[i]) {
            /* code modified by LLM (iteration 2): Call helper lemma and update count */
            SetCardinalityAddDigit(s, i);
            count := count + 1;
        } else {
            /* code modified by LLM (iteration 2): Call helper lemma */
            SetCardinalityAddNonDigit(s, i);
        }
        i := i + 1;
    }
}