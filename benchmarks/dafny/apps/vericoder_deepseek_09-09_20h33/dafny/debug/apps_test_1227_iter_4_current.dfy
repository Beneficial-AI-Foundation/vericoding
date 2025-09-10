function CountNonZeroDigits(n: int): int
    requires n >= 0
    ensures CountNonZeroDigits(n) >= 0
{
    if n == 0 then 0
    else if n % 10 == 0 then CountNonZeroDigits(n / 10)
    else 1 + CountNonZeroDigits(n / 10)
}

function CountNumbersWithKNonZeroDigits(n: int, k: int): int
    requires n >= 1
    requires k >= 1
    ensures CountNumbersWithKNonZeroDigits(n, k) >= 0
    ensures CountNumbersWithKNonZeroDigits(n, k) <= n
{
    CountRange(n, k, 1, n)
}

function CountRange(n: int, k: int, start: int, end: int): int
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    ensures CountRange(n, k, start, end) >= 0
    ensures CountRange(n, k, start, end) <= if start > end then 0 else end - start + 1
    decreases if end < start then 0 else end - start + 1
{
    if start > end then 0
    else if CountNonZeroDigits(start) == k then 
        1 + CountRange(n, k, start + 1, end)
    else 
        CountRange(n, k, start + 1, end)
}

predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1 && k <= 3
}

// <vc-helpers>
lemma CountRangeMonotonic(n: int, k: int, start: int, end: int, start2: int, end2: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    requires start2 >= 1
    requires end2 >= start2 - 1
    requires start <= start2
    requires end <= end2
    ensures CountRange(n, k, start, end) <= CountRange(n, k, start2, end2)
    decreases if start > end || start2 > end2 then 0 else (end2 - start2 + 1) + (end - start + 1)
{
    if start > end {
        assert CountRange(n, k, start, end) == 0;
    } else if start2 > end2 {
        assert CountRange(n, k, start2, end2) == 0;
    } else if start == start2 && end == end2 {
        // Base case: equal ranges
    } else {
        if start < start2 {
            // First range starts earlier, so we need to handle the prefix
            CountRangeMonotonic(n, k, start + 1, end, start2, end2);
            assert CountRange(n, k, start, end) == 
                (if CountNonZeroDigits(start) == k then 1 else 0) + CountRange(n, k, start + 1, end);
            assert CountRange(n, k, start2, end2) >= CountRange(n, k, start + 1, end);
        } else {
            // Same start point, but first range ends earlier
            CountRangeMonotonic(n, k, start, end, start, end2);
            assert CountRange(n, k, start, end2) == CountRange(n, k, start, end) + CountRange(n, k, end + 1, end2);
        }
    }
}

lemma CountRangeSplit(n: int, k: int, start: int, mid: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    requires mid >= start - 1 && mid <= end
    ensures CountRange(n, k, start, end) == CountRange(n, k, start, mid) + CountRange(n, k, mid + 1, end)
    decreases end - start + 1
{
    if start > end {
    } else if mid < start {
        assert CountRange(n, k, start, mid) == 0;
    } else if mid >= end {
        assert CountRange(n, k, mid + 1, end) == 0;
    } else {
        CountRangeSplit(n, k, start, mid, end - 1);
        if CountNonZeroDigits(end) == k {
            assert CountRange(n, k, start, end) == 1 + CountRange(n, k, start, end - 1);
            assert CountRange(n, k, start, end - 1) == CountRange(n, k, start, mid) + CountRange(n, k, mid + 1, end - 1);
            assert CountRange(n, k, mid + 1, end) == 1 + CountRange(n, k, mid + 1, end - 1);
        } else {
            assert CountRange(n, k, start, end) == CountRange(n, k, start, end - 1);
            assert CountRange(n, k, start, end - 1) == CountRange(n, k, start, mid) + CountRange(n, k, mid + 1, end - 1);
            assert CountRange(n, k, mid + 1, end) == CountRange(n, k, mid + 1, end - 1);
        }
    }
}

ghost method CountRangeDefinition(n: int, k: int, start: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    ensures CountRange(n, k, start, end) == (if start > end then 0 else 
        (if CountNonZeroDigits(start) == k then 1 else 0) + CountRange(n, k, start + 1, end))
    decreases if end < start then 0 else end - start + 1
{
    if start > end {
        return;
    }
    
    CountRangeDefinition(n, k, start + 1, end);
}
// </vc-helpers>

// <vc-spec>
method CountNumbersWithExactlyKNonZeroDigits(N: int, K: int) returns (count: int)
    requires ValidInput(N, K)
    ensures count == CountNumbersWithKNonZeroDigits(N, K)
    ensures count >= 0
    ensures count <= N
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 1;
    
    while i <= N
        invariant 1 <= i <= N + 1
        invariant count == CountRange(N, K, 1, i - 1)
        invariant count >= 0
        invariant count <= i - 1 <= N
    {
        CountRangeDefinition(N, K, 1, i - 1);
        if CountNonZeroDigits(i) == K {
            count := count + 1;
        }
        i := i + 1;
        if i <= N {
            CountRangeDefinition(N, K, 1, i - 1);
        }
    }
}
// </vc-code>

