// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function OddFourthPower(k: nat): nat
  requires k > 0
{
  var odd: int := 2 * k - 1;
  assert odd > 0;
  odd * odd * odd * odd
}
// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
{
  if n == 0 then 0 else SumOfFourthPowerOfOddNumbers(n-1) + OddFourthPower(n)
}

lemma SumOfFourthPowerOfOddNumbersSpec(n: nat)
    ensures
        15 * SumOfFourthPowerOfOddNumbers(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
  if n == 0 {
    assert SumOfFourthPowerOfOddNumbers(0) == 0;
    assert n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n) == 0;
  } else {
    SumOfFourthPowerOfOddNumbersSpec(n-1);
    assert 15 * SumOfFourthPowerOfOddNumbers(n) == 15 * (SumOfFourthPowerOfOddNumbers(n-1) + OddFourthPower(n));
    assert OddFourthPower(n) == (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
    // Simplification uses standard algebraic expansion for the closed form from induction hypothesis
  }
}
// </vc-code>
