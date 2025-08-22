//ATOM 
// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

//IMPL SumArray

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{
    s := 0;
    var i := 0;
    
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant s == Sum(xs[..i])
    {
        /* code modified by LLM (iteration 1): Added lemma call to establish Sum property when extending sequence by one element */
        SumExtendLemma(xs[..i], xs[i]);
        
        s := s + xs[i];
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): Fixed helper lemma with proper inductive proof structure */
lemma SumExtendLemma(prefix: seq<int>, x: int)
    ensures Sum(prefix + [x]) == Sum(prefix) + x
{
    var extended := prefix + [x];
    
    if |prefix| == 0 {
        /* code modified by LLM (iteration 1): Base case - empty prefix */
        assert extended == [x];
        assert Sum(extended) == Sum([x][..|[x]|-1]) + [x][|[x]|-1];
        assert Sum(extended) == Sum([]) + x;
        assert Sum(extended) == 0 + x;
    } else {
        /* code modified by LLM (iteration 1): Inductive case - prove by induction on prefix structure */
        var prefixPrefix := prefix[..|prefix|-1];
        var prefixLast := prefix[|prefix|-1];
        
        assert prefix == prefixPrefix + [prefixLast];
        assert extended == prefixPrefix + [prefixLast] + [x];
        assert extended == prefixPrefix + [prefixLast, x];
        
        /* code modified by LLM (iteration 1): Show that extended follows Sum's recursive pattern */
        assert |extended| >= 2;
        assert extended[..|extended|-1] == prefixPrefix + [prefixLast];
        assert extended[..|extended|-1] == prefix;
        assert extended[|extended|-1] == x;
        
        calc {
            Sum(extended);
            Sum(extended[..|extended|-1]) + extended[|extended|-1];
            Sum(prefix) + x;
        }
    }
}