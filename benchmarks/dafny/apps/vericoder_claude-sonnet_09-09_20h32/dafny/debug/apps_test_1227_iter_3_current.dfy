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
lemma CountRangeEqualsLoop(n: int, k: int, start: int, end: int, current: int, acc: int)
    requires n >= 1 && k >= 1
    requires start >= 1 && end >= start - 1
    requires current >= start && current <= end + 1
    requires acc >= 0
    requires acc == CountRange(n, k, start, current - 1)
    ensures acc + CountRange(n, k, current, end) == CountRange(n, k, start, end)
    decreases if end < current then 0 else end - current + 1
{
    if current > end {
        assert CountRange(n, k, current, end) == 0;
        assert CountRange(n, k, start, end) == CountRange(n, k, start, current - 1);
    } else {
        var newAcc := acc + (if CountNonZeroDigits(current) == k then 1 else 0);
        assert acc == CountRange(n, k, start, current - 1);
        if CountNonZeroDigits(current) == k {
            assert CountRange(n, k, start, current) == 1 + CountRange(n, k, start + 1, current);
            assert CountRange(n, k, start, current) == 1 + CountRange(n, k, start, current - 1);
            assert newAcc == acc + 1;
            assert newAcc == CountRange(n, k, start, current);
        } else {
            assert CountRange(n, k, start, current) == CountRange(n, k, start + 1, current);
            assert CountRange(n, k, start, current) == CountRange(n, k, start, current - 1);
            assert newAcc == acc;
            assert newAcc == CountRange(n, k, start, current);
        }
        CountRangeEqualsLoop(n, k, start, end, current + 1, newAcc);
    }
}

lemma CountRangeInvariant(n: int, k: int, start: int, end: int, i: int, count: int)
    requires n >= 1 && k >= 1
    requires start >= 1 && end >= start - 1
    requires start <= i <= end + 1
    requires count == CountRange(n, k, start, i - 1)
    ensures count >= 0
    ensures count <= if start > i - 1 then 0 else i - start
{
}

lemma CountRangeIncrement(n: int, k: int, i: int)
    requires n >= 1 && k >= 1
    requires i >= 1
    ensures CountRange(n, k, 1, i) == CountRange(n, k, 1, i - 1) + (if CountNonZeroDigits(i) == k then 1 else 0)
{
    if i == 1 {
        assert CountRange(n, k, 1, 0) == 0;
        if CountNonZeroDigits(1) == k {
            assert CountRange(n, k, 1, 1) == 1;
            assert CountRange(n, k, 1, 1) == 0 + 1;
        } else {
            assert CountRange(n, k, 1, 1) == 0;
            assert CountRange(n, k, 1, 1) == 0 + 0;
        }
    } else {
        assert i > 1;
        if CountNonZeroDigits(i) == k {
            assert CountRange(n, k, 1, i) == 1 + CountRange(n, k, 2, i);
            assert CountRange(n, k, 1, i - 1) == CountRange(n, k, 1, i - 1);
        } else {
            assert CountRange(n, k, 1, i) == CountRange(n, k, 2, i);
            assert CountRange(n, k, 1, i - 1) == CountRange(n, k, 1, i - 1);
        }
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
        invariant count == CountRange(N, K, 1, i - 1)
        invariant count >= 0
        invariant count <= i - 1
        decreases N - i + 1
    {
        CountRangeIncrement(N, K, i);
        if CountNonZeroDigits(i) == K {
            count := count + 1;
        }
        i := i + 1;
    }
    
    assert i == N + 1;
    assert count == CountRange(N, K, 1, N);
    assert CountNumbersWithKNonZeroDigits(N, K) == CountRange(N, K, 1, N);
}
// </vc-code>

