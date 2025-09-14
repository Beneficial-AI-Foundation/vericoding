// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>
predicate ValidRange(a: seq<int>, n: int) { 0 <= n <= |a| }
function SumAll(a: seq<int>): int { SumTo(a, |a|) }
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
  result := SumTo(a, |a|);
}
// </vc-code>
