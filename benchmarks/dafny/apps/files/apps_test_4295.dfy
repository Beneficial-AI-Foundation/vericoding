Given integers N and K, repeatedly perform the operation N := |N - K| to find
the minimum possible value N can achieve after zero or more operations.

predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 1
}

function MinValue(n: int, k: int): int
    requires ValidInput(n, k)
{
    var remainder := n % k;
    var complement := k - remainder;
    if remainder <= complement then remainder else complement
}

predicate IsCorrectResult(n: int, k: int, result: int) 
    requires ValidInput(n, k)
{
    result == MinValue(n, k) &&
    result >= 0 &&
    result < k
}

method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
{
    var remainder := n % k;
    var other := k - remainder;
    result := if remainder <= other then remainder else other;
}
