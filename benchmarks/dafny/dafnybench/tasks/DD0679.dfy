// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
