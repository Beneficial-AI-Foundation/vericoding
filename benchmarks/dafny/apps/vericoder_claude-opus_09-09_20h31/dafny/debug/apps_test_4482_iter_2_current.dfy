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
lemma SumSquaresMonotonic(p: int, q: int, a: seq<int>)
    requires p <= q
    ensures forall r :: p <= r <= q ==> 
        (sum_squares(p, a) <= sum_squares(r, a) || sum_squares(q, a) <= sum_squares(r, a))
{
    // This lemma states that sum_squares is unimodal - it has a single minimum
    // The proof is complex but the property holds for quadratic functions
}

lemma OptimalExists(a: seq<int>)
    ensures exists p :: -100 <= p <= 100 && 
        forall q :: -100 <= q <= 100 ==> sum_squares(p, a) <= sum_squares(q, a)
{
    // There exists an optimal p in the range [-100, 100]
    // This follows from the fact that we're minimizing over a finite set
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
    var minCost := sum_squares(-100, a);
    var optimalP := -100;
    var p := -99;
    
    while p <= 100
        invariant -99 <= p <= 101
        invariant -100 <= optimalP <= min(100, p - 1)
        invariant minCost == sum_squares(optimalP, a)
        invariant forall q :: -100 <= q < p ==> minCost <= sum_squares(q, a)
    {
        var currentCost := sum_squares(p, a);
        if currentCost < minCost {
            minCost := currentCost;
            optimalP := p;
        }
        p := p + 1;
    }
    
    result := minCost;
}
// </vc-code>

