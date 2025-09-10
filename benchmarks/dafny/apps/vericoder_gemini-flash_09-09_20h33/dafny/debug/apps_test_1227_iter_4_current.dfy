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
function CountNumbersWithKNonZeroDigits_Iterative(N: int, K: int): int
    requires N >= 0
    requires K >= 0
    ensures CountNumbersWithKNonZeroDigits_Iterative(N, K) >= 0
    ensures CountNumbersWithKNonZeroDigits_Iterative(N, K) <= N
{
    var count := 0;
    var i := 1;
    while i <= N
        invariant 0 <= i <= N + 1
        invariant 0 <= count <= i - 1
        invariant count == CountNumbersWithKNonZeroDigits_Iterative(i - 1, K)
    {
        if CountNonZeroDigits(i) == K
        {
            count := count + 1;
        }
        i := i + 1;
    }
    return count;
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
    var Cnt := 0;
    var i := 1;
    while i <= N
        invariant 0 <= Cnt <= i - 1
        invariant i >= 1
        invariant Cnt == CountNumbersWithKNonZeroDigits_Iterative(i - 1, K)
        decreases N - i
    {
        if CountNonZeroDigits(i) == K
        {
            Cnt := Cnt + 1;
        }
        i := i + 1;
    }
    return Cnt;
}
// </vc-code>

