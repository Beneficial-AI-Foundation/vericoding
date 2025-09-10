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
lemma ProveSumSquaresNonNegative(p: int, a: seq<int>)
    ensures sum_squares(p, a) >= 0
{
    if |a| == 0 {
    } else {
        ProveSumSquaresNonNegative(p, a[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
var min_val := sum_squares(-100, a);
ProveSumSquaresNonNegative(-100, a);
var best_p := -100;
var q := -99;
while (q <= 100)
    invariant -100 <= q <= 101
    invariant min_val == sum_squares(best_p, a)
    invariant -100 <= best_p <= q - 1
    invariant forall r :: -100 <= r < q ==> min_val <= sum_squares(r, a)
    invariant min_val >= 0
{
    var s := sum_squares(q, a);
    ProveSumSquaresNonNegative(q, a);
    if s < min_val {
        min_val := s;
        best_p := q;
    }
    q := q + 1;
}
result := min_val;
// </vc-code>

