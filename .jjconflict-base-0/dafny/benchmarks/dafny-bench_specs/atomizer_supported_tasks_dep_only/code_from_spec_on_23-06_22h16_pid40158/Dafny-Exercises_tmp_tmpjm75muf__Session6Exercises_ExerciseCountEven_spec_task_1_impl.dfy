// ATOM positive

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


// ATOM isEven

predicate isEven(x: int)
{
    x % 2 == 0
}

// ATOM CountEven

function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }


// ATOM ArrayFacts

lemma ArrayFacts()
{
    // Helper facts about arrays and sequences
}

/* code modified by LLM (iteration 1): Added helper lemma to establish positive property preservation */
lemma PositiveSlice(s: seq<int>, i: int)
requires positive(s) && 0 <= i <= |s|
ensures positive(s[..i])
{
}

/* code modified by LLM (iteration 1): Added helper lemma for CountEven increment property */
lemma CountEvenIncrement(s: seq<int>, i: int)
requires positive(s) && 0 <= i < |s|
ensures positive(s[..i+1])
ensures CountEven(s[..i+1]) == CountEven(s[..i]) + (if s[i] % 2 == 0 then 1 else 0)
{
    var slice := s[..i+1];
    assert slice[|slice|-1] == s[i];
    assert slice[..|slice|-1] == s[..i];
}

// IMPL mcountEven

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{
    n := 0;
    var i := 0;
    /* code modified by LLM (iteration 1): Added lemma call to establish initial positive property */
    PositiveSlice(v[..], 0);
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant positive(v[..i])
        invariant n == CountEven(v[..i])
    {
        /* code modified by LLM (iteration 1): Added lemma call to help prove invariant maintenance */
        CountEvenIncrement(v[..], i);
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
}