

// <vc-helpers>
lemma OddIndexLemma(k: int)
  requires k >= 0
  ensures 2*k + 1 == 2*(k+1) - 1
{
}

lemma SumOfFourthPowersFormula(n: int)
  requires n >= 0
  ensures (2*n+1)*(24*n*n*n - 12*n*n - 14*n + 7) == (2*n+1)*(24*n*n*n - 12*n*n - 14*n + 7)
{
}

ghost function SumOfFourthPowers(n: nat) : int
  decreases n
{
  if n == 0 then
    0
  else
    SumOfFourthPowers(n-1) + (2*n - 1)*(2*n - 1)*(2*n - 1)*(2*n - 1)
}
// </vc-helpers>

// <vc-spec>
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == SumOfFourthPowers(i)
    invariant SumOfFourthPowers(i) == i * (2 * i + 1) * (24 * i * i * i - 12 * i * i - 14 * i + 7) / 15
  {
    var odd := 2*i + 1;
    sum := sum + odd * odd * odd * odd;
    i := i + 1;
    if i < n {
      assert SumOfFourthPowers(i) == SumOfFourthPowers(i-1) + (2*i - 1)*(2*i - 1)*(2*i - 1)*(2*i - 1);
      assert SumOfFourthPowers(i) == (i-1) * (2*(i-1) + 1) * (24*(i-1)*(i-1)*(i-1) - 12*(i-1)*(i-1) - 14*(i-1) + 7) / 15 + (2*i - 1)*(2*i - 1)*(2*i - 1)*(2*i - 1);
    }
  }
}
// </vc-code>

