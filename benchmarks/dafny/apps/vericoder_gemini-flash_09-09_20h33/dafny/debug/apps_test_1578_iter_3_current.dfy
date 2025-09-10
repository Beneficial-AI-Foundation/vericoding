predicate ValidInput(n: int) {
    n >= 1
}

function MaxSum(n: int): int
    requires n >= 1
{
    n * (n - 1) / 2
}

// <vc-helpers>
function SumUpTo(k: int): int
    requires k >= 0
    ensures SumUpTo(k) == k * (k - 1) / 2
{
    if k == 0 then 0
    else if k > 0 then (k - 1) + SumUpTo(k - 1)
    else 0 // Should not be reached due to precondition k >= 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxSum(n)
// </vc-spec>
// <vc-code>
{
    var currentSum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant currentSum == SumUpTo(i)
    {
        currentSum := currentSum + i;
        i := i + 1;
    }
    result := currentSum;
}
// </vc-code>

