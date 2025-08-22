//ATOM Sum
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
        /* code modified by LLM (iteration 4): added lemma call before updating s to establish the relationship between Sum(xs[..i]) and Sum(xs[..i+1]) */
        SumExtendLemma(xs[..], i);
        s := s + xs[i];
        i := i + 1;
    }
}

/* code modified by LLM (iteration 4): fixed helper lemma with proper recursive proof to match Sum's definition */
lemma SumExtendLemma(xs: seq<int>, i: int)
    requires 0 <= i < |xs|
    ensures Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i]
{
    var prefix := xs[..i+1];
    if i == 0 {
        // Base case: Sum(xs[..1]) == Sum(xs[..0]) + xs[0]
        assert xs[..0] == [];
        assert Sum(xs[..0]) == 0;
        assert xs[..1] == [xs[0]];
        assert Sum(xs[..1]) == Sum([]) + xs[0] == 0 + xs[0] == xs[0];
    } else {
        // Recursive case: use the definition of Sum
        assert Sum(prefix) == Sum(prefix[..|prefix|-1]) + prefix[|prefix|-1];
        assert prefix[..|prefix|-1] == xs[..i];
        assert prefix[|prefix|-1] == xs[i];
    }
}