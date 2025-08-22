//ATOM
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//ATOM
function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }

//IMPL
/* code modified by LLM (iteration 3): Helper lemma to relate CountEven of prefix with extending from left */
lemma CountEvenPrefix(s: seq<int>, i: int)
    requires 0 <= i < |s|
    requires positive(s)
    ensures positive(s[..i])
    ensures positive(s[..i+1])
    ensures CountEven(s[..i+1]) == CountEven(s[..i]) + (if s[i] % 2 == 0 then 1 else 0)
{
    var prefix_i := s[..i];
    var prefix_i1 := s[..i+1];
    
    assert prefix_i1 == prefix_i + [s[i]];
    
    // Prove by induction on the structure that matches CountEven's recursion
    CountEvenAppendOne(prefix_i, s[i]);
}

/* code modified by LLM (iteration 3): Helper lemma for appending one element */
lemma CountEvenAppendOne(s: seq<int>, x: int)
    requires positive(s)
    requires x >= 0
    ensures positive(s + [x])
    ensures CountEven(s + [x]) == CountEven(s) + (if x % 2 == 0 then 1 else 0)
{
    var extended := s + [x];
    assert extended[|extended|-1] == x;
    assert extended[..|extended|-1] == s;
}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures n==CountEven(v[..])
{
    n := 0;
    var i := 0;
    
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant n == CountEven(v[..i])
        /* code modified by LLM (iteration 3): Strengthen invariant with positive property */
        invariant positive(v[..i])
    {
        /* code modified by LLM (iteration 3): Apply helper lemma to establish relationship */
        CountEvenPrefix(v[..], i);
        
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): Final assertion */
    assert i == v.Length;
    assert v[..i] == v[..];
}