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
lemma FactorsInDoubleFactorialTermination(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) >= 0
  decreases n
{
  if n <= 0 {
    return;
  }
  if n % 2 == 1 {
    if n - 1 >= 0 {
      FactorsInDoubleFactorialTermination(n - 1, p);
    }
  } else {
    if n / 2 >= 0 {
      FactorsInDoubleFactorialTermination(n / 2, p);
    }
  }
}

lemma FactorialVsDoubleFactorial(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) <= FactorsInFactorial(n, p)
  decreases n
{
  if n <= 0 {
    return;
  }
  
  if n % 2 == 1 {
    FactorialVsDoubleFactorial(n - 1, p);
    assert FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n, p) - FactorsInDoubleFactorial(n - 1, p);
    assert FactorsInDoubleFactorial(n, p) <= FactorsInFactorial(n, p);
  } else {
    FactorialVsDoubleFactorial(n / 2, p);
    if p == 2 {
      assert FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n / 2, p) + n / 2;
      assert FactorsInFactorial(n, p) >= FactorsInFactorial(n / 2, p) + n / 2;
    } else {
      assert FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n / 2, p);
      assert FactorsInFactorial(n, p) >= FactorsInFactorial(n / 2, p);
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
  var count2 := FactorsInDoubleFactorial(N, 2);
  var count5 := FactorsInDoubleFactorial(N, 5);
  
  // Call termination lemmas to help verification
  FactorsInDoubleFactorialTermination(N, 2);
  FactorsInDoubleFactorialTermination(N, 5);
  
  if count2 < count5 {
    result := count2;
  } else {
    result := count5;
  }
}
// </vc-code>

