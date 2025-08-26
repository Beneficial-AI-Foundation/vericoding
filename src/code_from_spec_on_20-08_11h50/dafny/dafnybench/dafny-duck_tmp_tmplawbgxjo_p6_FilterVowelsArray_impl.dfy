function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

// <vc-helpers>
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}

function CountVowels(xs: seq<char>): nat
{
    if |xs| == 0 then 0
    else if xs[|xs|-1] in vowels then CountVowels(xs[..|xs|-1]) + 1
    else CountVowels(xs[..|xs|-1])
}

lemma FilterVowelsLength(xs: seq<char>)
    ensures |FilterVowels(xs)| == CountVowels(xs)
{
    if |xs| == 0 {
    } else {
        FilterVowelsLength(xs[..|xs|-1]);
    }
}

lemma FilterVowelsPrefix(xs: seq<char>, i: nat)
    requires i <= |xs|
    ensures FilterVowels(xs[..i]) == FilterVowels(xs)[..CountVowels(xs[..i])]
{
    FilterVowelsLength(xs);
    FilterVowelsLength(xs[..i]);
    if i == 0 {
    } else {
        FilterVowelsPrefix(xs, i-1);
        FilterVowelsLength(xs[..i-1]);
        if xs[i-1] in vowels {
            assert xs[..i] == xs[..i-1] + [xs[i-1]];
            assert FilterVowels(xs[..i]) == FilterVowels(xs[..i-1]) + [xs[i-1]];
            assert CountVowels(xs[..i]) == CountVowels(xs[..i-1]) + 1;
            assert CountVowels(xs[..i-1]) <= CountVowels(xs);
            assert CountVowels(xs[..i]) <= CountVowels(xs);
        } else {
            assert xs[..i] == xs[..i-1] + [xs[i-1]];
            assert FilterVowels(xs[..i]) == FilterVowels(xs[..i-1]);
            assert CountVowels(xs[..i]) == CountVowels(xs[..i-1]);
        }
    }
}

lemma CountVowelsIncremental(xs: seq<char>, i: nat)
    requires 0 < i <= |xs|
    ensures CountVowels(xs[..i]) == CountVowels(xs[..i-1]) + (if xs[i-1] in vowels then 1 else 0)
{
    assert xs[..i] == xs[..i-1] + [xs[i-1]];
}

lemma FilterVowelsIncremental(xs: seq<char>, i: nat)
    requires 0 < i <= |xs|
    ensures FilterVowels(xs[..i]) == FilterVowels(xs[..i-1]) + (if xs[i-1] in vowels then [xs[i-1]] else [])
{
    assert xs[..i] == xs[..i-1] + [xs[i-1]];
}
// </vc-helpers>

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// <vc-code>
{
    var vowelCount := 0;
    var i := 0;
    
    // Count vowels
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant vowelCount == CountVowels(xs[..i])
    {
        if xs[i] in vowels {
            vowelCount := vowelCount + 1;
        }
        i := i + 1;
        if i <= xs.Length {
            CountVowelsIncremental(xs[..], i);
        }
    }
    
    FilterVowelsLength(xs[..]);
    
    // Create result array
    ys := new char[vowelCount];
    
    // Fill result array
    i := 0;
    var j := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= j <= vowelCount
        invariant j == CountVowels(xs[..i])
        invariant FilterVowels(xs[..i]) == ys[..j]
    {
        if xs[i] in vowels {
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
        if i <= xs.Length {
            CountVowelsIncremental(xs[..], i);
            FilterVowelsIncremental(xs[..], i);
        }
    }
}
// </vc-code>