Count the integers from 1 to N (inclusive) that have exactly K non-zero digits 
in their decimal representation. N can be very large (up to 10^100) and K is 
between 1 and 3.

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

function NumberOfDigits(n: int): int
    requires n >= 1
    ensures NumberOfDigits(n) >= 1
{
    if n < 10 then 1
    else 1 + NumberOfDigits(n / 10)
}

lemma CountRangeExtend(n: int, k: int, start: int, end: int)
    requires n >= 1 && k >= 1 && start >= 1 && end >= start - 1
    ensures CountRange(n, k, start, end + 1) == 
            CountRange(n, k, start, end) + (if end + 1 >= start && CountNonZeroDigits(end + 1) == k then 1 else 0)
    decreases if end < start then 0 else end - start + 1
{
    if start > end + 1 {
        return;
    }
    if start > end {
        return;
    }
    if start == end + 1 {
        return;
    }
    CountRangeExtend(n, k, start + 1, end);
}

method CountNumbersWithExactlyKNonZeroDigits(N: int, K: int) returns (count: int)
    requires ValidInput(N, K)
    ensures count == CountNumbersWithKNonZeroDigits(N, K)
    ensures count >= 0
    ensures count <= N
{
    count := 0;
    var i := 1;
    
    while i <= N
        invariant 1 <= i <= N + 1
        invariant count >= 0
        invariant count == CountRange(N, K, 1, i - 1)
    {
        ghost var oldCount := count;
        ghost var oldI := i;
        
        if CountNonZeroDigits(i) == K {
            count := count + 1;
        }
        i := i + 1;
        
        CountRangeExtend(N, K, 1, oldI - 1);
        assert count == CountRange(N, K, 1, oldI);
    }
}
