function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{
// </vc-spec>

// <vc-helpers>
lemma SumAppend(xs: seq<int>, i: int)
    requires 0 <= i < |xs|
    ensures Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i]
{
    var prefix := xs[..i+1];
    if i == 0 {
        assert prefix == [xs[0]];
        assert xs[..0] == [];
        assert Sum(xs[..0]) == 0;
        assert Sum(prefix) == Sum([]) + xs[0] == 0 + xs[0] == xs[0];
    } else {
        assert prefix == xs[..i] + [xs[i]];
        assert |prefix| == i + 1;
        assert prefix[..|prefix|-1] == xs[..i];
        assert prefix[|prefix|-1] == xs[i];
        assert Sum(prefix) == Sum(prefix[..|prefix|-1]) + prefix[|prefix|-1];
        assert Sum(prefix) == Sum(xs[..i]) + xs[i];
    }
}
// </vc-helpers>

// <vc-code>
    s := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant s == Sum(xs[..i])
    {
        SumAppend(xs[..], i);
        s := s + xs[i];
        i := i + 1;
    }
}
// </vc-code>