// <vc-preamble>
predicate ValidInput(n: int, k: int, t: int)
{
    1 <= n <= 1000000000 && 1 <= k <= n && 1 <= t < n + k
}

function CorrectResult(n: int, k: int, t: int): int
    requires ValidInput(n, k, t)
{
    if t <= k then t
    else if t > n then k + n - t
    else k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, t: int) returns (result: int)
    requires ValidInput(n, k, t)
    ensures result == CorrectResult(n, k, t)
    ensures 0 <= result <= k
// </vc-spec>
// <vc-code>
{
    if t <= k {
        result := t;
    } else if t > n {
        result := k + n - t;
    } else {
        result := k;
    }
}
// </vc-code>
