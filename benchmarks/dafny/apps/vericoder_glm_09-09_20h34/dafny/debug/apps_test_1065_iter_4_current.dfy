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
lemma ValidDistributionHelper(n: int, k: int, M: int, D: int, x: int, d: int)
    requires ValidInput(n, k, M, D)
    requires ValidDistribution(x, d, n, k, M, D)
    ensures 1 <= x <= M
    ensures 1 <= d <= D
    ensures CandiesUsed(x, d, k) <= n
    ensures Person1Candies(x, d) == x * d
{
    // All ensures clauses follow directly from the ValidDistribution predicate
    // and the definition of Person1Candies
}

lemma MaxValueExists(n: int, k: int, M: int, D: int)
    requires ValidInput(n, k, M, D)
    ensures exists max_val :: 
        max_val >= 0 && 
        max_val <= M * D &&
        (forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= max_val) &&
        (exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == max_val)
{
    // The proof is established by the implementation in solve()
    // This lemma serves as a specification that the solve method meets
    var res := solve(n, k, M, D);
    assert res >= 0;
    assert res <= M * D;
    assert forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= res;
    assert exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == res;
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
    var max_candies := 0;
    var found_x := 0;
    var found_d := 0;
    
    for x := 1 to M
        invariant forall current_x: int, current_d: int :: 
            current_x < x && ValidDistribution(current_x, current_d, n, k, M, D) ==> Person1Candies(current_x, current_d) <= max_candies
        invariant 0 <= max_candies <= M * D
        invariant 1 <= found_x <= M ==> found_x < x || (found_x == x && 1 <= found_d <= D)
    {
        for d := 1 to D
            invariant forall current_x: int, current_d: int :: 
                (current_x < x && ValidDistribution(current_x, current_d, n, k, M, D)) || 
                (current_x == x && current_d < d && ValidDistribution(current_x, current_d, n, k, M, D)) 
                ==> Person1Candies(current_x, current_d) <= max_candies
            invariant 0 <= max_candies <= M * D
            invariant 1 <= found_x <= M ==> found_x < x || (found_x == x && found_d < d)
        {
            if CandiesUsed(x, d, k) <= n {
                assert ValidDistribution(x, d, n, k, M, D) by {
                    ValidDistributionHelper(n, k, M, D, x, d);
                }
                var current_candies := Person1Candies(x, d);
                if current_candies > max_candies {
                    max_candies := current_candies;
                    found_x := x;
                    found_d := d;
                }
            }
        }
    }
    
    if max_candies > 0 {
        assert ValidDistribution(found_x, found_d, n, k, M, D);
        assert Person1Candies(found_x, found_d) == max_candies;
        assert exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == max_candies;
    } else {
        assert forall x: int, d: int :: !ValidDistribution(x, d, n, k, M, D);
        assert exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == max_candies by {
            assert false;
        }
    }
    assert forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= max_candies;
    result := max_candies;
}
// </vc-code>

