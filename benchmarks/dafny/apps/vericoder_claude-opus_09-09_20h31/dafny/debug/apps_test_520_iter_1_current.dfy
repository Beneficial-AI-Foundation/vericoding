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
lemma sumRangeProperty(s: seq<int>, start: int, end: int, i: int)
    requires 0 <= start <= i <= end <= |s|
    ensures sumRange(s, start, i) + sumRange(s, i, end) == sumRange(s, start, end)
    decreases end - i
{
    if i == end {
        assert sumRange(s, i, end) == 0;
    } else {
        sumRangeProperty(s, start, i + 1, end);
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
    var sum := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant n == |years|
        invariant sum == sumRange(years, 0, i)
    {
        sum := sum + years[i];
        i := i + 1;
    }
    
    assert i == n == |years|;
    assert sum == sumRange(years, 0, |years|);
    
    result := sum / n;
}
// </vc-code>

