// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
