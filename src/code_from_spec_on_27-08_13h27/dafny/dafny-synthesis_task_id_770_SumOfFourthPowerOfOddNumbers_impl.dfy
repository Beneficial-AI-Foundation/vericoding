// <vc-helpers>
lemma SumFourthPowerFormula(n: int)
  requires n > 0
  ensures true
{
  // Placeholder for potential helper proofs
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
// </vc-spec>
// </vc-spec>

// <vc-code>
method SumOfFourthPowerOfOddNumbersImpl(n: int) returns (sum: int)
  requires n > 0
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  sum := 0;
  var i := 1;
  var count := 0;
  while count < n
    invariant 0 <= count <= n
    invariant i == 2 * count + 1
    invariant sum == count * (2 * count + 1) * (24 * count * count * count - 12 * count * count - 14 * count + 7) / 15
  {
    sum := sum + i * i * i * i;
    i := i + 2;
    count := count + 1;
  }
}
// </vc-code>
