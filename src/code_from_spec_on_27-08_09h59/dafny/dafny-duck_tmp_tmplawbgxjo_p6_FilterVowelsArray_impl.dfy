//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

// <vc-helpers>
lemma FilterVowelsLength(xs: seq<char>)
    ensures |FilterVowels(xs)| <= |xs|
{
    if |xs| == 0 {
    } else if xs[|xs|-1] in vowels {
        FilterVowelsLength(xs[..|xs|-1]);
    } else {
        FilterVowelsLength(xs[..|xs|-1]);
    }
}

lemma FilterVowelsPreservesOrder(xs: seq<char>)
    ensures forall i :: 0 <= i < |FilterVowels(xs)| ==> FilterVowels(xs)[i] in vowels
{
    if |xs| == 0 {
    } else if xs[|xs|-1] in vowels {
        FilterVowelsPreservesOrder(xs[..|xs|-1]);
    } else {
        FilterVowelsPreservesOrder(xs[..|xs|-1]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    FilterVowelsLength(xs[..]);
    var result := new char[|FilterVowels(xs[..])|];
    var vowelSeq := FilterVowels(xs[..]);
    
    var i := 0;
    while i < |vowelSeq|
        invariant 0 <= i <= |vowelSeq|
        invariant forall j :: 0 <= j < i ==> result[j] == vowelSeq[j]
    {
        result[i] := vowelSeq[i];
        i := i + 1;
    }
    
    return result;
}
// </vc-code>
