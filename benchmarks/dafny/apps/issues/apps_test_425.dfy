// <vc-preamble>
predicate ValidInput(n: int, p: int)
{
    1 <= n <= 1000000000 && -1000 <= p <= 1000
}

predicate ValidResult(result: int)
{
    result == -1 || (0 <= result <= 5756)
}

predicate IsValidSolution(n: int, p: int, k: int)
{
    var target := n - k * p;
    target >= k && k >= CountBits(target)
}

predicate IsMinimalSolution(n: int, p: int, result: int)
{
    result != -1 ==> 
        (IsValidSolution(n, p, result) &&
         (forall k :: 0 <= k < result ==> !IsValidSolution(n, p, k)))
}

predicate NoSolutionExists(n: int, p: int)
{
    forall k :: 0 <= k <= 5756 ==> !IsValidSolution(n, p, k)
}

function CountBits(x: int): int
{
    if x <= 0 then 0
    else (x % 2) + CountBits(x / 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int) returns (result: int)
    requires ValidInput(n, p)
    ensures ValidResult(result)
    ensures result != -1 ==> IsValidSolution(n, p, result)
    ensures IsMinimalSolution(n, p, result)
    ensures result == -1 ==> NoSolutionExists(n, p)
// </vc-spec>
// <vc-code>
{
    assert n >= 1 ==> CountBits(n) > 0;

    var q := 0;
    while q <= 5756
        invariant 0 <= q <= 5757
        invariant forall k :: 0 <= k < q ==> !IsValidSolution(n, p, k)
    {
        var current_n := n - q * p;
        var popcount := CountBits(current_n);
        if current_n >= q && q >= popcount {
            assert IsValidSolution(n, p, q);
            return q;
        }
        assert !IsValidSolution(n, p, q);
        q := q + 1;
    }
    assert q == 5757;
    assert forall k :: 0 <= k <= 5756 ==> !IsValidSolution(n, p, k);
    return -1;
}
// </vc-code>
