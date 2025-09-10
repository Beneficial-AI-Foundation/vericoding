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
lemma ValidDistributionBounds(x: int, d: int, n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    requires ValidDistribution(x, d, n, k, M, D)
    ensures Person1Candies(x, d) <= M * D
{
    assert x <= M && d <= D;
    assert Person1Candies(x, d) == x * d;
}

lemma ExistsValidDistribution(n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D)
{
    assert ValidDistribution(1, 1, n, k, M, D);
}

lemma ValidDistributionExists(n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) >= 1
{
    assert ValidDistribution(1, 1, n, k, M, D);
    assert Person1Candies(1, 1) == 1;
}

lemma MaxCandiesBound(n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= M * D
{
    forall x: int, d: int | ValidDistribution(x, d, n, k, M, D)
        ensures Person1Candies(x, d) <= M * D
    {
        ValidDistributionBounds(x, d, n, k, M, D);
    }
}

lemma ExistsMaxCandy(n: int, k: int, M: int, D: int) returns (maxVal: int)
    requires ValidInput(n, k, M, D)
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == maxVal
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= maxVal
    ensures maxVal <= M * D
{
    var bestX := 1;
    var bestD := 1;
    maxVal := 1;
    
    var x := 1;
    while x <= M
        invariant 1 <= x <= M + 1
        invariant exists x': int, d': int :: ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
        invariant forall x': int, d': int :: (1 <= x' < x && ValidDistribution(x', d', n, k, M, D)) ==> Person1Candies(x', d') <= maxVal
        invariant maxVal <= M * D
    {
        var d := 1;
        while d <= D
            invariant 1 <= d <= D + 1
            invariant exists x': int, d': int :: ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
            invariant forall x': int, d': int :: (1 <= x' < x && ValidDistribution(x', d', n, k, M, D)) ==> Person1Candies(x', d') <= maxVal
            invariant forall d': int :: (1 <= d' < d && ValidDistribution(x, d', n, k, M, D)) ==> Person1Candies(x, d') <= maxVal
            invariant maxVal <= M * D
        {
            if CandiesUsed(x, d, k) <= n {
                var candies := Person1Candies(x, d);
                if candies > maxVal {
                    maxVal := candies;
                    bestX := x;
                    bestD := d;
                }
            }
            d := d + 1;
        }
        x := x + 1;
    }
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
    ExistsValidDistribution(n, k, M, D);
    MaxCandiesBound(n, k, M, D);
    var maxCandies := ExistsMaxCandy(n, k, M, D);
    result := maxCandies;
}
// </vc-code>

