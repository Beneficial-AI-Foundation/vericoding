function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
lemma SumToExpanded(a: array<int>, start: int, end: int)
    requires 0 <= start && start <= end && end <= a.Length
    ensures sumTo(a, start, end) == sumTo(a, start, start) + sumTo(a, start, end)
{
    if start == end {
        assert sumTo(a, start, end) == 0;
        assert sumTo(a, start, start) == 0;
    }
}

lemma SumToAddOne(a: array<int>, start: int, i: int)
    requires 0 <= start && start <= i && i < a.Length
    ensures sumTo(a, start, i+1) == sumTo(a, start, i) + a[i]
{
    // Proof by induction on the structure of sumTo
    if start == i+1 {
        assert sumTo(a, start, i+1) == 0;
        assert sumTo(a, start, i) == 0;
        assert a[i] == a[(i+1)-1];
    } else {
        assert i+1 > start;
        assert sumTo(a, start, i+1) == sumTo(a, start, (i+1)-1) + a[(i+1)-1];
        assert sumTo(a, start, (i+1)-1) == sumTo(a, start, i);
        assert a[(i+1)-1] == a[i];
    }
}
// </vc-helpers>

// <vc-spec>
method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
// </vc-spec>
// <vc-code>
{
    sum := 0;
    var i := start;
    
    while i < end
        invariant start <= i && i <= end
        invariant sum == sumTo(a, start, i)
    {
        sum := sum + a[i];
        SumToAddOne(a, start, i);
        i := i + 1;
    }
}
// </vc-code>

