// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed signature to (nat, nat) -> nat to fix type error */
function Power(base: nat, exp: nat): nat
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): no changes needed, fix was in helper signature */
{
  if n == 0 then 0
  else SumOfFourthPowerOfOddNumbers(n - 1) + Power(2 * n - 1, 4)
}
// </vc-code>
