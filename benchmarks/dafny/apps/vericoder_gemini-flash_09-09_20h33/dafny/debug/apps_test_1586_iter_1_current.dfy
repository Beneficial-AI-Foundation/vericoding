function ValidInput(N: int): bool
{
  N >= 0
}

function FactorsInFactorial(n: int, p: int): int
  requires p > 1
  requires n >= 0
  ensures FactorsInFactorial(n, p) >= 0
  ensures n == 0 ==> FactorsInFactorial(n, p) == 0
  ensures n > 0 ==> FactorsInFactorial(n, p) == n / p + FactorsInFactorial(n / p, p)
  decreases n
{
  if n == 0 then 0
  else n / p + FactorsInFactorial(n / p, p)
}

function FactorsInDoubleFactorial(n: int, p: int): int
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) >= 0
  ensures n <= 0 ==> FactorsInDoubleFactorial(n, p) == 0
  ensures n > 0 && n % 2 == 1 ==> FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n, p) - FactorsInDoubleFactorial(n - 1, p)
  ensures n > 0 && n % 2 == 0 ==> FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n / 2, p) + (if p == 2 then n / 2 else 0)
  decreases n
{
  if n <= 0 then 0
  else if n % 2 == 1 then
    FactorsInFactorial(n, p) - FactorsInDoubleFactorial(n - 1, p)
  else
    FactorsInFactorial(n / 2, p) + (if p == 2 then n / 2 else 0)
}

predicate ValidResult(N: int, result: int)
  requires N >= 0
{
  result >= 0 &&
  result == (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5))
}

// <vc-helpers>
function CountFactors(n: int, p: int): int
  requires p > 1
  requires n >= 0
  ensures CountFactors(n, p) >= 0
  decreases n
{
  if n == 0 then 0
  else n / p + CountFactors(n / p, p)
}

function CountDoubleFactorialFactors(n: int, p: int): int
  requires p > 1
  requires n >= 0
  ensures CountDoubleFactorialFactors(n, p) >= 0
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n % 2 == 0 then
    CountFactors(n / 2, p) + (if p == 2 then n / 2 else 0)
  else
    CountFactors(n, p) - CountDoubleFactorialFactors(n - 1, p)
}

lemma FactorsInFactorial_is_CountFactors(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInFactorial(n, p) == CountFactors(n, p)
  decreases n
{
  if n > 0 {
    FactorsInFactorial_is_CountFactors(n / p, p);
  }
}

lemma FactorsInDoubleFactorial_is_CountDoubleFactorialFactors(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) == CountDoubleFactorialFactors(n, p)
  decreases n
{
  if n > 0 {
    if n % 2 == 1 {
      FactorsInDoubleFactorial_is_CountDoubleFactorialFactors(n - 1, p);
      FactorsInFactorial_is_CountFactors(n, p);
    } else {
      FactorsInFactorial_is_CountFactors(n / 2, p);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidResult(N, result)
// </vc-spec>
// <vc-code>
{
  var count2: int := 0;
  var count5: int := 0;

  var temp_n := N;
  while temp_n >= 2 {
    count2 := count2 + temp_n / 2;
    temp_n := temp_n / 2;
  }

  temp_n := N;
  while temp_n >= 5 {
    count5 := count5 + temp_n / 5;
    temp_n := temp_n / 5;
  }

  FactorsInDoubleFactorial_is_CountDoubleFactorialFactors(N, 2);
  FactorsInDoubleFactorial_is_CountDoubleFactorialFactors(N, 5);

  if N == 0 || N == 1 {
    result := 0;
  } else if N % 2 == 0 {
    result := if count2 < count5 then count2 else count5;
  } else {
    var doubleFactorial2: int;
    var doubleFactorial5: int;

    doubleFactorial2 := FactorsInFactorial(N, 2) - FactorsInDoubleFactorial(N - 1, 2);
    doubleFactorial5 := FactorsInFactorial(N, 5) - FactorsInDoubleFactorial(N - 1, 5);

    result := if doubleFactorial2 < doubleFactorial5 then doubleFactorial2 else doubleFactorial5;
  }
}
// </vc-code>

