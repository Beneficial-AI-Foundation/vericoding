// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function sumOfSquaresOfFirstNOddNumbersFormula(n: nat): nat 
  requires n >= 0
  ensures sumOfSquaresOfFirstNOddNumbersFormula(n) as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
{
  if n == 0 then
    0
  else
    (2*n - 1)*(2*n - 1) + sumOfSquaresOfFirstNOddNumbersFormula(n - 1)
}

lemma SumOfSquaresLemma(n: nat)
  requires n >= 0
  ensures (sumOfSquaresOfFirstNOddNumbersFormula(n) as int) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
{
  if n != 0 {
    SumOfSquaresLemma(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
  SumOfSquaresLemma(n);
  result := sumOfSquaresOfFirstNOddNumbersFormula(n);
}
// </vc-code>
