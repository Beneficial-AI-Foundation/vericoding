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
lemma MaxExists(n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D)
{
    // Since M * D * k >= n, we know that x = 1, d = 1 is always valid
    assert CandiesUsed(1, 1, k) == 1 * ((1 - 1) * k + 1) == 1;
    assert 1 <= n;
    assert ValidDistribution(1, 1, n, k, M, D);
}

lemma CandiesUsedFormula(x: int, d: int, k: int)
    ensures CandiesUsed(x, d, k) == x * (d * k - k + 1)
{
    calc == {
        CandiesUsed(x, d, k);
        x * ((d - 1) * k + 1);
        x * (d * k - k + 1);
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
    var maxCandies := 0;
    var x := 1;
    
    MaxExists(n, k, M, D);
    assert ValidDistribution(1, 1, n, k, M, D);
    
    while x <= M
        invariant 1 <= x <= M + 1
        invariant 0 <= maxCandies <= M * D
        invariant forall xi: int, di: int :: 1 <= xi < x && 1 <= di <= D && ValidDistribution(xi, di, n, k, M, D) ==> Person1Candies(xi, di) <= maxCandies
        invariant exists xi: int, di: int :: ValidDistribution(xi, di, n, k, M, D) && Person1Candies(xi, di) == maxCandies
    {
        var d := 1;
        while d <= D
            invariant 1 <= d <= D + 1
            invariant 0 <= maxCandies <= M * D
            invariant forall xi: int, di: int :: (1 <= xi < x && 1 <= di <= D && ValidDistribution(xi, di, n, k, M, D)) || (xi == x && 1 <= di < d && ValidDistribution(xi, di, n, k, M, D)) ==> Person1Candies(xi, di) <= maxCandies
            invariant exists xi: int, di: int :: ValidDistribution(xi, di, n, k, M, D) && Person1Candies(xi, di) == maxCandies
        {
            if CandiesUsed(x, d, k) <= n {
                assert ValidDistribution(x, d, n, k, M, D);
                var candies := Person1Candies(x, d);
                if candies > maxCandies {
                    maxCandies := candies;
                }
            }
            d := d + 1;
        }
        x := x + 1;
    }
    
    result := maxCandies;
}
// </vc-code>

