// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min2(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// </vc-spec>
// <vc-code>
{
  min := min2(min2(a, b), c);
}
// </vc-code>
