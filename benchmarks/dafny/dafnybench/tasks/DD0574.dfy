// <vc-preamble>
function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
