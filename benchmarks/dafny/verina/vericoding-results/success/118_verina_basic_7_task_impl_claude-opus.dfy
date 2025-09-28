// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Simplified proof to avoid timeout */
function SumOfSquaresUpTo(k: nat): nat
{
  if k == 0 then 0
  else (2 * k - 1) * (2 * k - 1) + SumOfSquaresUpTo(k - 1)
}

lemma SumOfSquaresFormula(n: nat)
  ensures SumOfSquaresUpTo(n) as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
{
  if n == 0 {
  } else {
    SumOfSquaresFormula(n - 1);
    calc {
      SumOfSquaresUpTo(n) as int;
    == 
      (2 * n - 1) * (2 * n - 1) + SumOfSquaresUpTo(n - 1) as int;
    ==
      (2 * n as int - 1) * (2 * n as int - 1) + ((n - 1) as int * (2 * (n - 1) as int - 1) * (2 * (n - 1) as int + 1)) / 3;
    ==
      (2 * n as int - 1) * (2 * n as int - 1) + ((n - 1) as int * (2 * n as int - 3) * (2 * n as int - 1)) / 3;
    ==
      ((2 * n as int - 1) * (2 * n as int - 1) * 3 + (n - 1) as int * (2 * n as int - 3) * (2 * n as int - 1)) / 3;
    ==
      ((2 * n as int - 1) * (3 * (2 * n as int - 1) + (n - 1) as int * (2 * n as int - 3))) / 3;
    ==
      ((2 * n as int - 1) * (6 * n as int - 3 + 2 * n as int * n as int - 3 * n as int - 2 * n as int + 3)) / 3;
    ==
      ((2 * n as int - 1) * (2 * n as int * n as int + n as int)) / 3;
    ==
      ((2 * n as int - 1) * n as int * (2 * n as int + 1)) / 3;
    ==
      (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Call helper function and lemma */
{
  result := SumOfSquaresUpTo(n);
  SumOfSquaresFormula(n);
}
// </vc-code>
