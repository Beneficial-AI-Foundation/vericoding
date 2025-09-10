predicate ValidInput(n: int, k: int, M: int, D: int) {
    2 <= n && 2 <= k <= n && 1 <= M <= n && 1 <= D <= n && M * D * k >= n
}

function CandiesUsed(x: int, d: int, k: int): int {
    x * ((d - 1) * k + 1)
}

predicate ValidDistribution(x: int, d: int, n: int, k: int, M: int, D: int) {
    1 <= x <= M && 1 <= d <= D && CandiesUsed(x, d, k) <= n
}

function Person1Candies(x: int, d: int): int {
    x * d
}

// <vc-helpers>
function MaxCandiesPerson1(n: int, k: int, M: int, D: int): int
    requires ValidInput(n, k, M, D)
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == MaxCandiesPerson1(n, k, M, D)
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= MaxCandiesPerson1(n, k, M, D)
{
    var maxVal := 0;
    for x := 1 to M
        invariant 0 <= maxVal
        invariant forall x': int, d': int :: (1 <= x' <= x-1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
        invariant exists x': int, d': int :: (1 <= x' <= x-1 || x=1) && (1 <= d' <= D || x=1) && ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
    {
        for d := 1 to D
            invariant 0 <= maxVal
            invariant forall x': int, d': int :: (1 <= x' <= x-1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
            invariant forall d'': int :: (1 <= d'' <= d-1 && CandiesUsed(x, d'', k) <= n) ==> Person1Candies(x, d'') <= maxVal
            invariant exists x': int, d': int :: (1 <= x' <= x-1 || (x' == x && 1 <= d' <= d-1) || (x=1 && d=1)) && ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
        {
            if CandiesUsed(x, d, k) <= n {
                if Person1Candies(x, d) > maxVal {
                    maxVal := Person1Candies(x, d);
                }
            }
        }
    }
    maxVal
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, M: int, D: int) returns (result: int)
    requires ValidInput(n, k, M, D)
    ensures result >= 0
    ensures result <= M * D
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= result
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == result
// </vc-spec>
// <vc-code>
{
    var maxVal := 0;
    for x := 1 to M
        invariant 0 <= maxVal
        invariant ValidInput(n, k, M, D)
        invariant forall x': int, d': int :: (1 <= x' <= x-1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
        invariant exists xOther: int, dOther: int :: (1 <= xOther <= x-1 || (x=1 && xOther=1)) && (1 <= dOther <= D || (x=1 && dOther=1)) && ValidDistribution(xOther, dOther, n, k, M, D) && Person1Candies(xOther, dOther) == maxVal
    {
        for d := 1 to D
            invariant 0 <= maxVal
            invariant ValidInput(n, k, M, D)
            invariant forall xp: int, dp: int ::
                ( (1 <= xp <= x-1 && 1 <= dp <= D) || (xp == x && 1 <= dp <= d-1) ) &&
                CandiesUsed(xp, dp, k) <= n
                ==> Person1Candies(xp, dp) <= maxVal
            invariant exists xOther: int, dOther: int :: (1 <= xOther <= x-1 || (xOther == x && 1 <= dOther <= d-1) || (x=1 && d=1 && xOther=1 && dOther=1)) && ValidDistribution(xOther, dOther, n, k, M, D) && Person1Candies(xOther, dOther) == maxVal
        {
            if CandiesUsed(x, d, k) <= n {
                if Person1Candies(x, d) > maxVal {
                    maxVal := Person1Candies(x, d);
                }
            }
        }
    }
    result := maxVal;
}
// </vc-code>

