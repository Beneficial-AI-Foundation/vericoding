predicate ValidInput(n: int, m: int, k: int)
{
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

predicate ValidOutput(n: int, m: int, lane: int, desk: int, side: string)
{
    1 <= lane <= n && 1 <= desk <= m && (side == "L" || side == "R")
}

predicate CorrectSolution(n: int, m: int, k: int, lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
}

// <vc-helpers>
lemma lemma_k_minus_1_ge_0(k: int)
    requires k >= 1
    ensures k - 1 >= 0
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
    ensures ValidOutput(n, m, lane, desk, side)
    ensures CorrectSolution(n, m, k, lane, desk, side)
// </vc-spec>
// <vc-code>
{
    var k_minus_1 := k - 1;
    lemma_k_minus_1_ge_0(k);
    lane := k_minus_1 / (2 * m) + 1;
    var remainder_2m := k_minus_1 % (2 * m);
    desk := remainder_2m / 2 + 1;
    if remainder_2m % 2 == 0
    {
        side := "L";
    }
    else
    {
        side := "R";
    }
}
// </vc-code>

