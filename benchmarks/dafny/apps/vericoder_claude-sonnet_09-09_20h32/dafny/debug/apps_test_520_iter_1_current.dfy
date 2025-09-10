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
lemma SumRangeComplete(s: seq<int>)
    ensures sumRange(s, 0, |s|) == sumRange(s, 0, |s|)
{
}

lemma SumRangeEqualsSum(s: seq<int>, total: int)
    requires total == sumRange(s, 0, |s|)
    ensures total == sumRange(s, 0, |s|)
{
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
        total := total + years[i];
        i := i + 1;
    }
    
    result := total / n;
}
// </vc-code>

