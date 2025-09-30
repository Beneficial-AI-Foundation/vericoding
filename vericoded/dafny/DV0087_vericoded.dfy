// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumOfSquaresUpTo(k: nat): nat
{
  if k == 0 then 0
  else (2 * k - 1) * (2 * k - 1) + SumOfSquaresUpTo(k - 1)
}

lemma SumOfSquaresFormula(n: nat)
  ensures SumOfSquaresUpTo(n) as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
{
  if n == 0 {
    assert SumOfSquaresUpTo(0) == 0;
    assert (0 * (-1) * 1) / 3 == 0;
  } else {
    SumOfSquaresFormula(n - 1);
    var prev := SumOfSquaresUpTo(n - 1) as int;
    var curr := (2 * n as int - 1) * (2 * n as int - 1);
    assert SumOfSquaresUpTo(n) as int == prev + curr;
    assert prev == ((n - 1) as int * (2 * (n - 1) as int - 1) * (2 * (n - 1) as int + 1)) / 3;
    assert prev == ((n - 1) as int * (2 * n as int - 3) * (2 * n as int - 1)) / 3;
    var target := (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3;
    assert target - prev == (n as int * (2 * n as int - 1) * (2 * n as int + 1) - (n - 1) as int * (2 * n as int - 3) * (2 * n as int - 1)) / 3;
    assert target - prev == ((2 * n as int - 1) * (n as int * (2 * n as int + 1) - (n - 1) as int * (2 * n as int - 3))) / 3;
    assert n as int * (2 * n as int + 1) - (n - 1) as int * (2 * n as int - 3) == 2 * n as int * n as int + n as int - (2 * n as int * n as int - 3 * n as int - 2 * n as int + 3);
    assert n as int * (2 * n as int + 1) - (n - 1) as int * (2 * n as int - 3) == 2 * n as int * n as int + n as int - 2 * n as int * n as int + 3 * n as int + 2 * n as int - 3;
    assert n as int * (2 * n as int + 1) - (n - 1) as int * (2 * n as int - 3) == 6 * n as int - 3;
    assert target - prev == ((2 * n as int - 1) * (6 * n as int - 3)) / 3;
    assert (6 * n as int - 3) == 3 * (2 * n as int - 1);
    assert target - prev == ((2 * n as int - 1) * 3 * (2 * n as int - 1)) / 3;
    assert target - prev == (2 * n as int - 1) * (2 * n as int - 1);
    assert target - prev == curr;
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
  result := SumOfSquaresUpTo(n);
  SumOfSquaresFormula(n);
}
// </vc-code>
