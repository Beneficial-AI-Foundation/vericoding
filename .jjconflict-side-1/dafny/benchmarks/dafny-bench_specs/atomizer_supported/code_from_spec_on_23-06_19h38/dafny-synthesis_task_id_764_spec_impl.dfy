// ATOM 
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

//IMPL CountDigits
method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
    count := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 1): Added helper lemma to establish relationship between counting and set cardinality */
    ghost var digitIndices := set j: int | 0 <= j < 0 && IsDigit(s[j]);
    assert digitIndices == {};
    assert |digitIndices| == 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 0 <= j < i && IsDigit(s[j])|
    {
        /* code modified by LLM (iteration 1): Added ghost variable and assertions to track set relationship */
        ghost var oldDigitIndices := set j: int | 0 <= j < i && IsDigit(s[j]);
        ghost var newDigitIndices := set j: int | 0 <= j < i + 1 && IsDigit(s[j]);
        
        if IsDigit(s[i]) {
            /* code modified by LLM (iteration 1): Added assertion to prove set cardinality relationship */
            assert newDigitIndices == oldDigitIndices + {i};
            assert i !in oldDigitIndices;
            SetCardinalityLemma(oldDigitIndices, i);
            count := count + 1;
        } else {
            /* code modified by LLM (iteration 1): Added assertion for non-digit case */
            assert newDigitIndices == oldDigitIndices;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): Added helper lemma to prove set cardinality properties */
lemma SetCardinalityLemma<T>(s: set<T>, x: T)
    requires x !in s
    ensures |s + {x}| == |s| + 1
{
    // Dafny can prove this automatically
}