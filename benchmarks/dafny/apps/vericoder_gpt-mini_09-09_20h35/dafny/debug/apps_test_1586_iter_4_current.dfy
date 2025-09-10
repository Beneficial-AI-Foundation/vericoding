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
lemma TrivialSubst(N: int, a: int, b: int)
  requires N >= 0
  requires a == FactorsInDoubleFactorial(N, 2)
  requires b == FactorsInDoubleFactorial(N, 5)
  ensures (if a < b then a else b) == (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5))
{
  if a < b {
    // From a == F2 and b == F5 we get F2 < F5
    assert FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5);
    // Both sides reduce to F2
    assert (if a < b then a else b) == a;
    assert a == FactorsInDoubleFactorial(N, 2);
    assert (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5)) == FactorsInDoubleFactorial(N, 2);
    assert (if a < b then a else b) == (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5));
  } else {
    // From a == F2 and b == F5 we get not (F2 < F5)
    assert !(FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5));
    // Both sides reduce to F5
    assert (if a < b then a else b) == b;
    assert b == FactorsInDoubleFactorial(N, 5);
    assert (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5)) == FactorsInDoubleFactorial(N, 5);
    assert (if a < b then a else b) == (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5));
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
  var a := FactorsInDoubleFactorial(N, 2);
  var b := FactorsInDoubleFactorial(N, 5);
  result := if a < b then a else b;
  assert a >= 0;
  assert b >= 0;
  assert result >= 0;
  assert result == (if a < b then a else b);
  TrivialSubst(N, a, b);
  assert result == (if FactorsInDoubleFactorial(N, 2) < FactorsInDoubleFactorial(N, 5) then FactorsInDoubleFactorial(N, 2) else FactorsInDoubleFactorial(N, 5));
}
// </vc-code>

