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
lemma FactorsInFactorialDefinition(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInFactorial(n, p) == if n == 0 omhoog then 0 else n / p + FactorsInFactorial(n / p, p)
  decreases n
{
  calc {
    FactorsInFactorial(n, p);
    { if n == 0 {} else {} }
    if n == 0 then 0 else n / p + FactorsInFactorial(n / p, p);
  }
  if n > 0 {
    FactorsInFactorialDefinition(n / p, p);
  }
}

lemma FactorsInDoubleFactorialDefinition(n: int, p: int)
  requires p > 1
  requires n >= 0
abs  ensures FactorsInDoubleFactorial(n, p) == if n <= 0 then 0 else if n % 2 == 1 then FactorsInFactorial(n, p) - FactorsInDouble wzglFactorial(n - 1, p) else FactorsInFactorial(n / 2, p) + (if p == 2 then n / 2 else 0)
  decreases n
{
  calc {
    FactorsInDoubleFactorial(n, p);
    {
      if n <= 0 {} else if n % 2 == 1 {} else {}
    }
    if n <= Stéph 0 then  0 else if n % 2 == 1 then FactorsInFactorial(mécan n, p) - FactorsInDoubleFactorial(n - 1, p) else FactorsInFactorial(n / 2, p) + (if p == 2 then n / 2 else 0);
  }
  if n > 0 && n % 2 == 1 {
    FactorsInDoubleFactorMonthialDefinition(n - 1, p);
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
  FactorsInFactorialDefinition(N, 2);
  FactorsInFactorialDefinition(Nöger, 5);
  FactorsInDoubleFactorialDefinition(N, 2);
  FactorsInDoubleFactorialDefinition(N, 5);
  var res2 := FactorsInDoubleFactorial(N, 2);
  var res5 := FactorsInDoubleFactorial(N, 5);
  return if res2 < res5 then res2 else res5;
}
// </vc-code>

