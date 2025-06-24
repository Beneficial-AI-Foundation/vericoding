//Given an array of characters, it filters all the vowels. ['d','e','l','i','g','h','t']-> ['e','i']
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

//ATOM 
//Given an array of characters, it filters all the vowels. ['d','e','l','i','g','h','t']-> ['e','i']

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

/* code modified by LLM (iteration 3): added helper function that processes left to right to match loop */
function FilterVowelsLeftToRight(s: seq<char>, n: int): seq<char>
    requires 0 <= n <= |s|
{
    if n == 0 then []
    else 
        var rest := FilterVowelsLeftToRight(s, n-1);
        if s[n-1] in vowels then rest + [s[n-1]]
        else rest
}

/* code modified by LLM (iteration 3): strengthened lemma to establish equivalence between the two approaches */
lemma FilterVowelsEquivalence(s: seq<char>)
    ensures FilterVowels(s) == FilterVowelsLeftToRight(s, |s|)
{
    if |s| == 0 {
        // base case
    } else {
        FilterVowelsEquivalence(s[..|s|-1]);
        
        var prefix := s[..|s|-1];
        var last := s[|s|-1];
        
        // Show that both functions handle the last element the same way
        assert s == prefix + [last];
        assert FilterVowelsLeftToRight(s, |s|-1) == FilterVowelsLeftToRight(prefix, |prefix|);
        assert FilterVowels(prefix) == FilterVowelsLeftToRight(prefix, |prefix|);
    }
}

/* code modified by LLM (iteration 3): added lemma to help with loop invariant proof */
lemma FilterVowelsLeftToRightBuilding(s: seq<char>, n: int, vowelSeq: seq<char>)
    requires 0 <= n <= |s|
    requires vowelSeq == FilterVowelsLeftToRight(s, n)
    requires n < |s|
    ensures if s[n] in vowels then FilterVowelsLeftToRight(s, n+1) == vowelSeq + [s[n]]
            else FilterVowelsLeftToRight(s, n+1) == vowelSeq
{
    // This follows directly from the definition of FilterVowelsLeftToRight
}

//IMPL 
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{
    var vowelSeq: seq<char> := [];
    var i := 0;
    
    /* code modified by LLM (iteration 3): updated loop with better invariant and proof steps */
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant vowelSeq == FilterVowelsLeftToRight(xs[..], i)
    {
        /* code modified by LLM (iteration 3): added lemma call before loop body modification */
        FilterVowelsLeftToRightBuilding(xs[..], i, vowelSeq);
        
        if xs[i] in vowels {
            vowelSeq := vowelSeq + [xs[i]];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): use equivalence lemma to establish postcondition */
    FilterVowelsEquivalence(xs[..]);
    
    ys := new char[|vowelSeq|];
    i := 0;
    while i < |vowelSeq|
        invariant 0 <= i <= |vowelSeq|
        invariant forall j :: 0 <= j < i ==> ys[j] == vowelSeq[j]
    {
        ys[i] := vowelSeq[i];
        i := i + 1;
    }
}