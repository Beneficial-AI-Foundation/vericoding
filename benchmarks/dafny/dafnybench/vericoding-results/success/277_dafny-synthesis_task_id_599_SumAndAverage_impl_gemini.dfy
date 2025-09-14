// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Sum(k: int): int
  requires k >= 0
{
  if k == 0 then 0 else Sum(k - 1) + k
}

lemma SumFormula(k: int)
  requires k >= 0
  ensures Sum(k) == k * (k + 1) / 2
{
  if k > 0 {
    SumFormula(k - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == Sum(i)
  {
    i := i + 1;
    sum := sum + i;
  }
  SumFormula(n);
  average := sum as real / n as real;
}
// </vc-code>
