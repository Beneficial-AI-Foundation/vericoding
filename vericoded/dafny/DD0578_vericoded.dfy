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
    decreases |xs|
{
    if |xs| == 0 {
    } else if xs[|xs|-1] in vowels {
        FilterVowelsLength(xs[..|xs|-1]);
    } else {
        FilterVowelsLength(xs[..|xs|-1]);
    }
}

lemma FilterVowelsAppend(xs: seq<char>, c: char)
    ensures FilterVowels(xs + [c]) == if c in vowels then FilterVowels(xs) + [c] else FilterVowels(xs)
{
    assert xs + [c] == (xs + [c])[..|(xs + [c])|-1] + [(xs + [c])[|(xs + [c])|-1]];
    assert (xs + [c])[..|(xs + [c])|-1] == xs;
    assert (xs + [c])[|(xs + [c])|-1] == c;
}

lemma FilterVowelsPrefix(xs: seq<char>, i: int)
    requires 0 <= i <= |xs|
    ensures i < |xs| ==> FilterVowels(xs[..i+1]) == if xs[i] in vowels then FilterVowels(xs[..i]) + [xs[i]] else FilterVowels(xs[..i])
    decreases |xs| - i
{
    if i < |xs| {
        assert xs[..i+1] == xs[..i] + [xs[i]];
        FilterVowelsAppend(xs[..i], xs[i]);
    }
}

lemma FilterVowelsStrictlyIncreasing(xs: seq<char>, i: int)
    requires 0 <= i < |xs|
    requires xs[i] in vowels
    ensures |FilterVowels(xs[..i])| < |FilterVowels(xs[..i+1])|
{
    FilterVowelsPrefix(xs, i);
    assert FilterVowels(xs[..i+1]) == FilterVowels(xs[..i]) + [xs[i]];
    assert |FilterVowels(xs[..i+1])| == |FilterVowels(xs[..i])| + 1;
}

lemma FilterVowelsMonotonic(xs: seq<char>, i: int, j: int)
    requires 0 <= i <= j <= |xs|
    ensures |FilterVowels(xs[..i])| <= |FilterVowels(xs[..j])|
{
    if i == j {
        assert xs[..i] == xs[..j];
    } else {
        FilterVowelsMonotonic(xs, i, j-1);
        FilterVowelsPrefix(xs, j-1);
        if xs[j-1] in vowels {
            assert FilterVowels(xs[..j]) == FilterVowels(xs[..j-1]) + [xs[j-1]];
        } else {
            assert FilterVowels(xs[..j]) == FilterVowels(xs[..j-1]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    
    // Count vowels
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant count == |FilterVowels(xs[..i])|
    {
        FilterVowelsPrefix(xs[..], i);
        if xs[i] in vowels {
            count := count + 1;
        }
        i := i + 1;
    }
    
    assert xs[..i] == xs[..xs.Length] == xs[..];
    assert count == |FilterVowels(xs[..])|;
    
    ys := new char[count];
    var j := 0;
    i := 0;
    
    // Copy vowels to result array
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= j <= ys.Length
        invariant j == |FilterVowels(xs[..i])|
        invariant ys.Length == count == |FilterVowels(xs[..])|
        invariant ys[..j] == FilterVowels(xs[..i])
    {
        FilterVowelsPrefix(xs[..], i);
        if xs[i] in vowels {
            assert j < ys.Length by {
                FilterVowelsStrictlyIncreasing(xs[..], i);
                assert |FilterVowels(xs[..i])| < |FilterVowels(xs[..i+1])|;
                FilterVowelsMonotonic(xs[..], i+1, xs.Length);
                assert |FilterVowels(xs[..i+1])| <= |FilterVowels(xs[..])|;
            }
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert xs[..] == xs[..xs.Length];
    assert j == ys.Length;
    assert ys[..] == ys[..ys.Length] == FilterVowels(xs[..]);
}
// </vc-code>

