predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1 && n <= 100 && k <= 100
}

function MinCrackerDifference(n: int, k: int): int
    requires k > 0
{
    if n % k == 0 then 0 else 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result == MinCrackerDifference(n, k)
    ensures result == 0 <==> n % k == 0
    ensures result == 1 <==> n % k != 0
// </vc-spec>
// <vc-code>
{
    if n % k == 0 {
        result := 0;
    } else {
        result := 1;
    }
}
// </vc-code>

