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
    if M > 0 && D > 0
    { // Ensure loops have at least one iteration for initial validDistribution
        if CandiesUsed(1, 1, k) <= n
        {
            maxVal := Person1Candies(1, 1);
        } else {
            // Find a valid initial value if (1,1) is not valid
            var found_valid_initial := false;
            for x_init := 1 to M {
                for d_init := 1 to D {
                    if CandiesUsed(x_init, d_init, k) <= n {
                        maxVal := Person1Candies(x_init, d_init);
                        found_valid_initial := true;
                        break;
                    }
                }
                if found_valid_initial { break; }
            }
        }
    }


    for x_idx := 1 to M
        invariant 0 <= maxVal
        invariant forall x': int, d': int :: (1 <= x' <= x_idx - 1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
        invariant exists x': int, d': int :: ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
    {
        for d_idx := 1 to D
            invariant 0 <= maxVal
            invariant forall x': int, d': int :: (1 <= x' <= x_idx - 1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
            invariant forall d'': int :: (1 <= d'' <= d_idx - 1 && CandiesUsed(x_idx, d'', k) <= n) ==> Person1Candies(x_idx, d'') <= maxVal
            invariant exists x': int, d': int :: ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == maxVal
        {
            if CandiesUsed(x_idx, d_idx, k) <= n {
                if Person1Candies(x_idx, d_idx) > maxVal {
                    maxVal := Person1Candies(x_idx, d_idx);
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
    if M > 0 && D > 0
    { // Ensure loops have at least one iteration for initial validDistribution
        if CandiesUsed(1, 1, k) <= n
        {
            maxVal := Person1Candies(1, 1);
        } else {
            // Find a valid initial value if (1,1) is not valid
            var found_valid_initial := false;
            for x_init := 1 to M {
                for d_init := 1 to D {
                    if CandiesUsed(x_init, d_init, k) <= n {
                        maxVal := Person1Candies(x_init, d_init);
                        found_valid_initial := true;
                        break;
                    }
                }
                if found_valid_initial { break; }
            }
        }
    }

    for x_idx := 1 to M
        invariant 0 <= maxVal
        invariant ValidInput(n, k, M, D)
        invariant forall x': int, d': int :: (1 <= x' <= x_idx - 1 && 1 <= d' <= D && CandiesUsed(x', d', k) <= n) ==> Person1Candies(x', d') <= maxVal
        invariant exists xOther: int, dOther: int :: ValidDistribution(xOther, dOther, n, k, M, D) && Person1Candies(xOther, dOther) == maxVal
    {
        for d_idx := 1 to D
            invariant 0 <= maxVal
            invariant ValidInput(n, k, M, D)
            invariant forall xp: int, dp: int ::
                ( (1 <= xp <= x_idx - 1 && 1 <= dp <= D) || (xp == x_idx && 1 <= dp <= d_idx - 1) ) &&
                CandiesUsed(xp, dp, k) <= n
                ==> Person1Candies(xp, dp) <= maxVal
            invariant exists xOther: int, dOther: int :: ValidDistribution(xOther, dOther, n, k, M, D) && Person1Candies(xOther, dOther) == maxVal
        {
            if CandiesUsed(x_idx, d_idx, k) <= n {
                if Person1Candies(x_idx, d_idx) > maxVal {
                    maxVal := Person1Candies(x_idx, d_idx);
                }
            }
        }
    }
    result := maxVal;
}
// </vc-code>

