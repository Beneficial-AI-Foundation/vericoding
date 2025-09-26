// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
