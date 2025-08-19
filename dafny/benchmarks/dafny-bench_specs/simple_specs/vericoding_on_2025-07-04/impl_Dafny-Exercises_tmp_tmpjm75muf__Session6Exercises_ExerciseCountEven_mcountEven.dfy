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
/* code modified by LLM (iteration 3): Simplified helper function to count from start index */
function CountEvenFrom(s: seq<int>, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then 0
    else (if s[start] % 2 == 0 then 1 else 0) + CountEvenFrom(s, start + 1)
}

/* code modified by LLM (iteration 3): Lemma to prove equivalence between CountEven and CountEvenFrom */
lemma CountEvenEquivalence(s: seq<int>)
    requires positive(s)
    ensures CountEven(s) == CountEvenFrom(s, 0)
{
    if s == [] {
        // Base case
    } else {
        // Inductive case
        assert s == s[0..1] + s[1..];
        assert s[..|s|-1] == s[0..|s|-1];
        CountEvenEquivalence(s[..|s|-1]);
        CountEvenFromSplit(s, 0, |s|-1);
    }
}

/* code modified by LLM (iteration 3): Helper lemma for splitting CountEvenFrom */
lemma CountEvenFromSplit(s: seq<int>, start: int, split: int)
    requires 0 <= start <= split <= |s|
    requires positive(s)
    ensures CountEvenFrom(s, start) == CountEvenFrom(s[start..split], 0) + CountEvenFrom(s, split)
    decreases split - start
{
    if start == split {
        // Base case
    } else {
        CountEvenFromSplit(s, start + 1, split);
    }
}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures n==CountEven(v[..])
{
    n := 0;
    var i := 0;
    /* code modified by LLM (iteration 3): Fixed loop invariant using CountEvenFrom */
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant n == CountEvenFrom(v[..], 0) - CountEvenFrom(v[..], i)
    {
        if v[i] % 2 == 0 {
            n := n + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 3): Apply equivalence lemma */
    CountEvenEquivalence(v[..]);
}