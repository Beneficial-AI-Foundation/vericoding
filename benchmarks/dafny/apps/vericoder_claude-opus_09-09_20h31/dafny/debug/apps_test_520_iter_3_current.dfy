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
lemma sumRangeProperty(s: seq<int>, start: int, i: int, end: int)
    requires 0 <= start <= i <= end <= |s|
    ensures sumRange(s, start, i) + sumRange(s, i, end) == sumRange(s, start, end)
    decreases i - start
{
    if start == i {
        assert sumRange(s, start, i) == 0;
        assert sumRange(s, start, i) + sumRange(s, i, end) == 0 + sumRange(s, i, end) == sumRange(s, i, end);
        assert sumRange(s, start, end) == sumRange(s, i, end);
    } else {
        assert sumRange(s, start, i) == s[start] + sumRange(s, start + 1, i);
        assert sumRange(s, start, end) == s[start] + sumRange(s, start + 1, end);
        sumRangeProperty(s, start + 1, i, end);
        assert sumRange(s, start + 1, i) + sumRange(s, i, end) == sumRange(s, start + 1, end);
        assert s[start] + sumRange(s, start + 1, i) + sumRange(s, i, end) == s[start] + sumRange(s, start + 1, end);
        assert sumRange(s, start, i) + sumRange(s, i, end) == sumRange(s, start, end);
    }
}

lemma sumRangeAppend(s: seq<int>, start: int, end: int)
    requires 0 <= start <= end < |s|
    ensures sumRange(s, start, end + 1) == sumRange(s, start, end) + s[end]
    decreases end - start
{
    if start == end {
        assert sumRange(s, start, end) == 0;
        assert sumRange(s, start, end + 1) == s[start];
        assert s[start] == s[end];
    } else {
        assert sumRange(s, start, end + 1) == s[start] + sumRange(s, start + 1, end + 1);
        sumRangeAppend(s, start + 1, end);
        assert sumRange(s, start + 1, end + 1) == sumRange(s, start + 1, end) + s[end];
        assert sumRange(s, start, end) == s[start] + sumRange(s, start + 1, end);
        assert sumRange(s, start, end + 1) == sumRange(s, start, end) + s[end];
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
        sumRangeAppend(years, 0, i);
        assert sumRange(years, 0, i + 1) == sumRange(years, 0, i) + years[i];
        sum := sum + years[i];
        i := i + 1;
    }
    
    assert i == n == |years|;
    assert sum == sumRange(years, 0, |years|);
    
    result := sum / n;
}
// </vc-code>

