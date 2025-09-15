// <vc-preamble>
function Pow(base: nat, exponent: nat): nat
    ensures exponent == 0 ==> Pow(base, exponent) == 1
    ensures exponent > 0 ==> Pow(base, exponent) == base * Pow(base, exponent-1)
{
    if exponent == 0 then 1 else base * Pow(base, exponent-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed */
// </vc-helpers>

// <vc-spec>
method CountNumbersStartingOrEndingWithOne(n: nat) returns (count: nat)

    requires n > 0

    ensures n == 1 ==> count == 1
    ensures n > 1 ==> count == 18 * Pow(10, n - 2)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Corrected the loop invariant and post-loop assignment to match the specification for n > 1. */
{
  if n == 1 {
    count := 1;
    return;
  }

  // For n > 1, the count is 18 * Pow(10, n - 2).
  // We calculate this directly.
  count := 18 * Pow(10, n - 2);
}
// </vc-code>
