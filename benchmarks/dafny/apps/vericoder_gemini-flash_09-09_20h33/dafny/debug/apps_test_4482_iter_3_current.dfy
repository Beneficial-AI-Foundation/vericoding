function sum_squares(p: int, a: seq<int>): int
{
    if |a| == 0 then 0
    else (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..])
}

predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && n <= 100 && |a| == n && 
    forall i :: 0 <= i < |a| ==> -100 <= a[i] <= 100
}

predicate IsOptimalCost(result: int, a: seq<int>)
{
    result >= 0 &&
    exists p :: -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall p :: -100 <= p <= 100 ==> result <= sum_squares(p, a)
}

// <vc-helpers>
function sum_squares_iter(p: int, a: seq<int>, i: int): int
    requires 0 <= i <= |a|
    decreases |a| - i
{
    if i == |a| then 0
    else (p - a[i]) * (p - a[i]) + sum_squares_iter(p, a, i + 1)
}

lemma sum_squares_eq_sum_squares_iter(p: int, a: seq<int>)
    ensures sum_squares(p, a) == sum_squares_iter(p, a, 0)
{
    if |a| == 0 {
        assert sum_squares(p, a) == 0;
        assert sum_squares_iter(p, a, 0) == 0;
    } else {
        calc {
            sum_squares(p, a);
            (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..]);
            {
                sum_squares_eq_sum_squares_iter(p, a[1..]);
            }
            (p - a[0]) * (p - a[0]) + sum_squares_iter(p, a[1..], 0);
            sum_squares_iter(p, a, 0);
        }
    }
}

lemma sum_squares_non_negative(p: int, a: seq<int>)
    ensures sum_squares(p, a) >= 0
{
    if |a| == 0 {
        assert sum_squares(p, a) == 0;
    } else {
        var term := (p - a[0]) * (p - a[0]);
        assert term >= 0;
        sum_squares_non_negative(p, a[1..]);
        assert sum_squares(p, a[1..]) >= 0;
        assert sum_squares(p, a) == term + sum_squares(p, a[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
    var min_cost := sum_squares(0, a); // Initialize with cost for p=0
    sum_squares_eq_sum_squares_iter(0, a); // Proof for initial assignment
    sum_squares_non_negative(0, a);

    var p_optimal := 0;

    ghost var min_cost_ghost := min_cost;
    ghost var p_optimal_ghost := p_optimal;

    for p' := -100 to 100
        invariant -100 <= p' <= 101
        invariant min_cost == min_cost_ghost
        invariant p_optimal == p_optimal_ghost
        invariant (exists p_found :: -100 <= p_found < p' && min_cost_ghost == sum_squares(p_found, a)) || p' == -100
        invariant forall x :: -100 <= x < p' ==> min_cost_ghost <= sum_squares(x, a)
    {
        var current_cost := sum_squares(p', a);
        sum_squares_eq_sum_squares_iter(p', a); // Proof for current_cost calculation
        sum_squares_non_negative(p', a);

        if current_cost < min_cost_ghost {
            min_cost_ghost := current_cost;
            p_optimal_ghost := p';
        }
    }

    result := min_cost_ghost;

    // Post-condition proof: result >= 0
    assert result >= 0 by { sum_squares_non_negative(p_optimal_ghost, a); } ;

    // Post-condition proof: exists p :: -100 <= p <= 100 && result == sum_squares(p, a)
    assert -100 <= p_optimal_ghost <= 100;
    assert result == sum_squares(p_optimal_ghost, a);

    // Post-condition proof: forall p :: -100 <= p <= 100 ==> result <= sum_squares(p, a)
    forall p'' | -100 <= p'' <= 100
        ensures result <= sum_squares(p'', a)
    {
        // This holds because `min_cost_ghost` was updated to be the minimum found.
        assert sum_squares(p_optimal_ghost, a) <= sum_squares(p'', a);
    }
}
// </vc-code>

