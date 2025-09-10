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
lemma CountRangeSplit(n: int, k: int, start: int, mid: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires mid >= start
    requires end >= mid - 1
    ensures CountRange(n, k, start, end) == 
            CountRange(n, k, start, mid - 1) + CountRange(n, k, mid, end)
    decreases end - start + 1
{
    if start > end {
        assert CountRange(n, k, start, end) == 0;
        assert CountRange(n, k, start, mid - 1) == 0;
        assert CountRange(n, k, mid, end) == 0;
    } else if start == mid {
        assert CountRange(n, k, start, mid - 1) == 0;
    } else if start < mid {
        if CountNonZeroDigits(start) == k {
            assert CountRange(n, k, start, end) == 1 + CountRange(n, k, start + 1, end);
            CountRangeSplit(n, k, start + 1, mid, end);
        } else {
            assert CountRange(n, k, start, end) == CountRange(n, k, start + 1, end);
            CountRangeSplit(n, k, start + 1, mid, end);
        }
    }
}

lemma CountRangeExtend(n: int, k: int, start: int, end: int)
    requires n >= 1
    requires k >= 1
    requires start >= 1
    requires end >= start - 1
    ensures CountRange(n, k, start, end + 1) == 
            CountRange(n, k, start, end) + CountRange(n, k, end + 1, end + 1)
    ensures CountRange(n, k, start, end + 1) == 
            CountRange(n, k, start, end) + 
            (if CountNonZeroDigits(end + 1) == k then 1 else 0)
{
    if start > end + 1 {
        assert CountRange(n, k, start, end + 1) == 0;
        assert CountRange(n, k, start, end) == 0;
        assert CountRange(n, k, end + 1, end + 1) == 0;
    } else {
        CountRangeSplit(n, k, start, end + 1, end + 1);
        assert CountRange(n, k, end + 1, end + 1) == 
               if CountNonZeroDigits(end + 1) == k then 1 else 0;
    }
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
        invariant count >= 0
        invariant count == CountRange(N, K, 1, i - 1)
        invariant count <= i - 1
    {
        if CountNonZeroDigits(i) == K {
            count := count + 1;
        }
        
        CountRangeExtend(N, K, 1, i - 1);
        assert CountRange(N, K, 1, i) == 
               CountRange(N, K, 1, i - 1) + 
               (if CountNonZeroDigits(i) == K then 1 else 0);
        
        i := i + 1;
    }
    
    assert i == N + 1;
    assert count == CountRange(N, K, 1, N);
    assert count == CountNumbersWithKNonZeroDigits(N, K);
}
// </vc-code>

