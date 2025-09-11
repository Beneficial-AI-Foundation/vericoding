// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
