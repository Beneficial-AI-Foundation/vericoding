// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Add proper syntax and verification */
function SumOfFourthPowerOfOddNumbersHelper(n: nat): nat {
  if n == 0 then 0 else SumOfFourthPowerOfOddNumbersHelper(n - 1) + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1)
}

lemma SumLemma(n: nat)
  ensures 15 * SumOfFourthPowerOfOddNumbersHelper(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
  if n == 0 {
  } else {
    SumLemma(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix syntax error in if statement */
{
  if n == 0 then 0 else SumOfFourthPowerOfOddNumbers(n - 1) + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1)
}

lemma SumOfFourthPowerOfOddNumbersSpec(n: nat)
    ensures
        15 * SumOfFourthPowerOfOddNumbers(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
  SumLemma(n);
}
// </vc-code>
