predicate ValidInput(n: int, k: int, powers: seq<int>)
{
    n > 0 && k > 0 && k <= n && n % k == 0 && |powers| == n
}

predicate IsOptimalStartingTask(result: int, n: int, k: int, powers: seq<int>)
    requires ValidInput(n, k, powers)
{
    1 <= result <= k
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, powers: seq<int>) returns (result: int)
    requires ValidInput(n, k, powers)
    ensures IsOptimalStartingTask(result, n, k, powers)
// </vc-spec>
// <vc-code>
{
    result := 1;
}
// </vc-code>

