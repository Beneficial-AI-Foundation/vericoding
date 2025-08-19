predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//ATOM
function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }

//IMPL
/* code modified by LLM (iteration 3): Added helper function to count even numbers from start */
function CountEvenFromStart(s: seq<int>, i: int): int
    requires positive(s)
    requires 0 <= i <= |s|
{
    if i == 0 then 0
    else CountEvenFromStart(s, i-1) + (if s[i-1] % 2 == 0 then 1 else 0)
}

/* code modified by LLM (iteration 3): Fixed lemma to properly establish equivalence with correct inductive proof */
lemma CountEvenPrefix(s: seq<int>, i: int)
    requires positive(s)
    requires 0 <= i <= |s|
    ensures CountEven(s[..i]) == CountEvenFromStart(s, i)
{
    if i == 0 {
        assert s[..0] == [];
    } else {
        CountEvenPrefix(s, i-1);
        assert s[..i] == s[..i-1] + [s[i-1]];
        assert s[..i][..i-1] == s[..i-1];
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
        /* code modified by LLM (iteration 3): Updated invariant to use helper function */
        invariant n == CountEvenFromStart(v[..], i)
    {
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 3): Added lemma call and assertion to establish postcondition */
    CountEvenPrefix(v[..], v.Length);
    assert v[..v.Length] == v[..];
    assert n == CountEvenFromStart(v[..], v.Length);
    assert CountEven(v[..]) == CountEvenFromStart(v[..], v.Length);
}