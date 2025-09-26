// <vc-preamble>
predicate ValidInput(k2: int, k3: int, k5: int, k6: int)
{
    k2 >= 0 && k3 >= 0 && k5 >= 0 && k6 >= 0 &&
    k2 <= 5000000 && k3 <= 5000000 && k5 <= 5000000 && k6 <= 5000000
}

function OptimalSum(k2: int, k3: int, k5: int, k6: int): int
    requires ValidInput(k2, k3, k5, k6)
{
    var count256 := min(min(k2, k5), k6);
    var remaining_k2 := k2 - count256;
    var count32 := min(k3, remaining_k2);
    256 * count256 + 32 * count32
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(k2: int, k3: int, k5: int, k6: int) returns (result: int)
    requires ValidInput(k2, k3, k5, k6)
    ensures result >= 0
    ensures result == OptimalSum(k2, k3, k5, k6)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
