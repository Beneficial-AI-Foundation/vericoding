predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//ATOM
function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }

//IMPL
/* code modified by LLM (iteration 4): Added helper function that counts even numbers from start */
function CountEvenHelper(s: seq<int>, k: int): int
    requires positive(s)
    requires 0 <= k <= |s|
{
    if k == 0 then 0
    else CountEvenHelper(s, k-1) + (if s[k-1] % 2 == 0 then 1 else 0)
}

/* code modified by LLM (iteration 4): Fixed lemma with correct sequence manipulation */
lemma CountEvenEquiv(s: seq<int>, k: int)
    requires positive(s)
    requires 0 <= k <= |s|
    ensures CountEven(s[..k]) == CountEvenHelper(s, k)
{
    if k == 0 {
        assert s[..k] == [];
    } else {
        var prefix := s[..k];
        var shorterPrefix := s[..k-1];
        
        // Key insight: prefix is shorterPrefix + [s[k-1]]
        assert prefix == shorterPrefix + [s[k-1]];
        
        // Recursive call establishes the relationship for k-1
        CountEvenEquiv(s, k-1);
        
        // Now we need to show CountEven(shorterPrefix + [s[k-1]]) relates correctly
        // The CountEven function works from the end, so:
        assert prefix[|prefix|-1] == s[k-1];
        assert prefix[..|prefix|-1] == shorterPrefix;
        
        calc {
            CountEven(prefix);
            CountEven(shorterPrefix + [s[k-1]]);
            (if (shorterPrefix + [s[k-1]])[|(shorterPrefix + [s[k-1]])|-1] % 2 == 0 then 1 else 0) + CountEven((shorterPrefix + [s[k-1]])[..|(shorterPrefix + [s[k-1]])|-1]);
            (if s[k-1] % 2 == 0 then 1 else 0) + CountEven(shorterPrefix);
            (if s[k-1] % 2 == 0 then 1 else 0) + CountEvenHelper(s, k-1); // by inductive hypothesis
            CountEvenHelper(s, k);
        }
    }
}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures n==CountEven(v[..])
{
    n := 0;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        /* code modified by LLM (iteration 4): Invariant using helper function */
        invariant n == CountEvenHelper(v[..], i)
    {
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): Apply lemma to prove final assertion */
    CountEvenEquiv(v[..], v.Length);
    assert n == CountEven(v[..]);
}