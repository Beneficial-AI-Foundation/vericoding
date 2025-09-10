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
lemma FactorsInFactorialTermination(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures n / p < n || n == 0
{
  if n > 0 {
    assert p > 1;
    assert n / p < n;
  }
}

lemma FactorsInDoubleFactorialTermination(n: int)
  requires n > 0
  ensures n - 1 < n
  ensures n / 2 < n
{
}

lemma FactorsInFactorialNonNegative(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInFactorial(n, p) >= 0
  decreases n
{
  if n == 0 {
    assert FactorsInFactorial(n, p) == 0;
  } else {
    FactorsInFactorialNonNegative(n / p, p);
    assert FactorsInFactorial(n / p, p) >= 0;
    assert n / p >= 0;
    assert FactorsInFactorial(n, p) == n / p + FactorsInFactorial(n / p, p) >= 0;
  }
}

lemma FactorsInDoubleFactorialNonNegative(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) >= 0
  decreases n
{
  if n <= 0 {
    assert FactorsInDoubleFactorial(n, p) == 0;
  } else if n % 2 == 1 {
    FactorsInFactorialNonNegative(n, p);
    FactorsInDoubleFactorialNonNegative(n - 1, p);
  } else {
    FactorsInFactorialNonNegative(n / 2, p);
  }
}

lemma MinProperty(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures (if a < b then a else b) >= 0
  ensures (if a < b then a else b) <= a
  ensures (if a < b then a else b) <= b
{
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidResult(N, result)
// </vc-spec>
// <vc-code>
{
  FactorsInDoubleFactorialNonNegative(N, 2);
  FactorsInDoubleFactorialNonNegative(N, 5);
  
  var factors2 := FactorsInDoubleFactorial(N, 2);
  var factors5 := FactorsInDoubleFactorial(N, 5);
  
  MinProperty(factors2, factors5);
  
  if factors2 < factors5 {
    result := factors2;
  } else {
    result := factors5;
  }
}
// </vc-code>

