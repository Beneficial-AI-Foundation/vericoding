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
// no additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
    var total := 0;
    for i := 0 to |a| {
        total := total + a[i];
    }
    var mean_low := total / n;
    var mean_high := mean_low + 1;
    var s_low := sum_squares(mean_low, a);
    var s_high := sum_squares(mean_high, a);
    if s_low <= s_high {
        result := s_low;
    } else {
        result := s_high;
    }
    if mean_low - 1 >= -100 {
        var s_lower := sum_squares(mean_low - 1, a);
        if s_lower < result {
            result := s_lower;
        }
    }
    if mean_high + 1 <= 100 {
        var s_upper := sum_squares(mean_high + 1, a);
        if s_upper < result {
            result := s_upper;
        }
    }
}
// </vc-code>

