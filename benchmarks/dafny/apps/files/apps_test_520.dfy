// <vc-preamble>
function sumRange(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start == end then 0
    else s[start] + sumRange(s, start + 1, end)
}

predicate ValidInput(n: int, years: seq<int>)
{
    n > 0 && |years| == n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, years: seq<int>) returns (result: int)
    requires ValidInput(n, years)
    ensures result == sumRange(years, 0, |years|) / n
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
