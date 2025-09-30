// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

// <vc-helpers>
lemma SumAppend(xs: seq<int>, y: int)
    ensures Sum(xs + [y]) == Sum(xs) + y
{
    if |xs| == 0 {
        assert xs + [y] == [y];
    } else {
        calc {
            Sum(xs + [y]);
            == Sum((xs + [y])[..|xs + [y]|-1]) + (xs + [y])[|xs + [y]|-1];
            == Sum(xs) + y;
        }
    }
}

lemma SumPrefix(xs: seq<int>, i: int)
    requires 0 <= i <= |xs|
    ensures Sum(xs[..i]) + (if i < |xs| then xs[i] else 0) == (if i < |xs| then Sum(xs[..i+1]) else Sum(xs[..i]))
{
    if i < |xs| {
        assert xs[..i+1] == xs[..i] + [xs[i]];
        SumAppend(xs[..i], xs[i]);
    }
}
// </vc-helpers>

// <vc-spec>
method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
// </vc-spec>
// <vc-code>
{
    s := 0;
    var i := 0;
    
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant s == Sum(xs[..i])
    {
        s := s + xs[i];
        SumPrefix(xs[..], i);
        i := i + 1;
    }
    
    assert xs[..] == xs[..xs.Length];
}
// </vc-code>

