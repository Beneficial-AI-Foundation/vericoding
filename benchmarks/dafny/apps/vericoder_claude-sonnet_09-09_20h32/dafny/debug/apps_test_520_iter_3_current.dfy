function sumRange(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start == end then 0
    else s[start] + sumRange(s, start + 1, end)
}

predicate ValidInput(n: int, years: seq<int>)
{
    n > 0 && |years| == n
}

// <vc-helpers>
lemma SumRangeExtend(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures sumRange(s, 0, i + 1) == sumRange(s, 0, i) + s[i]
{
    if i == 0 {
        assert sumRange(s, 0, 1) == s[0] + sumRange(s, 1, 1);
        assert sumRange(s, 1, 1) == 0;
        assert sumRange(s, 0, 0) == 0;
    } else {
        assert sumRange(s, 0, i + 1) == s[0] + sumRange(s, 1, i + 1);
        assert sumRange(s, 0, i) == s[0] + sumRange(s, 1, i);
        SumRangeExtend(s[1..], i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, years: seq<int>) returns (result: int)
    requires ValidInput(n, years)
    ensures result == sumRange(years, 0, |years|) / n
// </vc-spec>
// <vc-code>
{
    var total := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant total == sumRange(years, 0, i)
    {
        SumRangeExtend(years, i);
        total := total + years[i];
        i := i + 1;
    }
    
    assert i == n;
    assert total == sumRange(years, 0, n);
    assert n == |years|;
    assert total == sumRange(years, 0, |years|);
    result := total / n;
}
// </vc-code>

