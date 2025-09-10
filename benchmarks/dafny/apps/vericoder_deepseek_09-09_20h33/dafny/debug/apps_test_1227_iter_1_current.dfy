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
{
}

lemma CountRangeSplit(n: int, k: int, start: int, mid: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    requires mid >= start - 1 && mid <= end + 1
    ensures CountRange(n, k, start, end) == CountRange(n, k, start, mid) + CountRange(n, k, mid + 1, end)
{
    if start > end {
    } else if mid < start {
    } else if mid >= end {
    } else {
        CountRangeSplit(n, k, start + 1, mid, end);
    }
}

ghost method CountRangeDefinition(n: int, k: int, start: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    decreases if end < start then 0 else end - start + 1
{
    if start > end {
        return;
    }
    
    // Recursive call to verify the recursive case
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
        if CountNonZeroDigits(i) == K {
            count := count + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

