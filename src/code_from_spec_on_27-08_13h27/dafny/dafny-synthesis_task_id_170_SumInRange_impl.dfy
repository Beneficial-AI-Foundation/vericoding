function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma SumInRangeLemma(a: array<int>, start: int, end: int)
    requires 0 <= start && start <= end && end <= a.Length
    ensures sumTo(a, start, end) == SumArraySegment(a, start, end)
    decreases end - start
{
    if start == end {
        assert sumTo(a, start, end) == 0;
        assert SumArraySegment(a, start, end) == 0;
    } else {
        SumInRangeLemma(a, start, end - 1);
        assert sumTo(a, start, end) == sumTo(a, start, end - 1) + a[end - 1];
        assert SumArraySegment(a, start, end) == SumArraySegment(a, start, end - 1) + a[end - 1];
    }
}

function SumArraySegment(a: array<int>, start: int, end: int): int
    requires 0 <= start && start <= end && end <= a.Length
    decreases end - start
    reads a
{
    if start == end then 0 else a[end - 1] + SumArraySegment(a, start, end - 1)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeSumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
{
    sum := 0;
    var i := start;
    while i < end
        invariant start <= i <= end
        invariant sum == sumTo(a, start, i)
    {
        sum := sum + a[i];
        i := i + 1;
    }
    SumInRangeLemma(a, start, end);
    assert sum == sumTo(a, start, end);
}
// </vc-code>
