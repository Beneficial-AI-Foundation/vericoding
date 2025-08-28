// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

// <vc-helpers>
lemma SumSliceProperty(xs: seq<int>, i: int)
    requires 0 <= i <= |xs|
    ensures Sum(xs[..i]) == if i == 0 then 0 else Sum(xs[..i-1]) + xs[i-1]
{
    if i == 0 {
        assert xs[..0] == [];
        assert Sum(xs[..0]) == Sum([]) == 0;
    } else {
        assert xs[..i] == xs[..i-1] + [xs[i-1]];
        assert Sum(xs[..i]) == Sum(xs[..i-1] + [xs[i-1]]);
        assert Sum(xs[..i-1] + [xs[i-1]]) == Sum(xs[..i-1]) + xs[i-1];
    }
}

lemma SumAppendProperty(xs: seq<int>, x: int)
    ensures Sum(xs + [x]) == Sum(xs) + x
{
    if |xs| == 0 {
        assert xs + [x] == [x];
        assert Sum([x]) == Sum([]) + x == 0 + x;
    } else {
        var n := |xs|;
        assert (xs + [x])[n] == x;
        assert (xs + [x])[..n] == xs;
        assert Sum(xs + [x]) == Sum((xs + [x])[..n]) + (xs + [x])[n];
        assert Sum(xs + [x]) == Sum(xs) + x;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    s := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant s == Sum(xs[..i])
    {
        assert xs[..i+1] == xs[..i] + [xs[i]];
        SumAppendProperty(xs[..i], xs[i]);
        assert Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i];
        s := s + xs[i];
        i := i + 1;
    }
}
// </vc-code>
