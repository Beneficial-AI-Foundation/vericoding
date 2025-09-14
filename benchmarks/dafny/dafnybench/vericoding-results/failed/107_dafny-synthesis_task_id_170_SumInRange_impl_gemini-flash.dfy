function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

// <vc-helpers>
function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    decreases (end - start)
    reads a
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

function SumInRange_decreases(a: array<int>, start: int, end: int) : (nat)
    reads a
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
{
    end - start
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
    if start == end {
        return 0;
    } else if start + 1 == end {
        return a[start];
    } else {
        // Here we know end - start >= 2.
        // We choose mid such that start < mid < end.
        // A common choice for divide and conquer is (start + end) / 2.
        // If end - start >= 2, then start + 1 <= end - 1.
        // (start + end) / 2 will always be >= (start + start + 2) / 2 = start + 1. So mid > start.
        // And (start + end) / 2 will always be <= (end - 2 + end) / 2 = end - 1. So mid < end.
        var mid := (start + end) / 2;
        assert start < mid && mid < end; // This assertion holds given end - start >= 2.

        // The recursive calls now satisfy the termination metric.
        // SumInRange_decreases(a, start, mid) == mid - start, and mid - start < end - start because mid < end.
        // SumInRange_decreases(a, mid, end) == end - mid, and end - mid < end - start because start < mid.
        var leftSum := SumInRange(a, start, mid);
        var rightSum := SumInRange(a, mid, end);
        return leftSum + rightSum;
    }
}
// </vc-code>

