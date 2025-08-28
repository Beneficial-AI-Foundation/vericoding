function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma SumToInvariant(a: array<int>, start: int, end: int, i: int, currentSum: int)
    requires a != null
    requires 0 <= start <= i <= end <= a.Length
    requires currentSum == sumTo(a, start, i)
    ensures currentSum + sumTo(a, i, end) == sumTo(a, start, end)
    decreases end - i
{
    if i == end {
        assert sumTo(a, i, end) == 0;
    } else {
        SumToInvariant(a, start, end, i+1, currentSum + a[i]);
        assert sumTo(a, i, end) == a[i] + sumTo(a, i+1, end);
    }
}

lemma SumToStep(a: array<int>, start: int, i: int)
    requires 0 <= start <= i < a.Length
    ensures sumTo(a, start, i+1) == sumTo(a, start, i) + a[i]
{
    assert sumTo(a, start, i+1) == sumTo(a, start, i) + a[i];
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
{
    sum := 0;
    var i := start;
    
    while i < end
        invariant start <= i <= end
        invariant sum == sumTo(a, start, i)
    {
        SumToStep(a, start, i);
        sum := sum + a[i];
        i := i + 1;
    }
}
// </vc-code>
