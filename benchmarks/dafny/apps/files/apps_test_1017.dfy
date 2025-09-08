Given n stones, find the maximum number of distributions such that no two
consecutive distributions contain the same number of stones. Each distribution
must contain at least 1 stone.

predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
{
    if n % 3 == 0 {
        result := 2 * (n / 3);
    } else {
        result := 2 * (n / 3) + 1;
    }
}
