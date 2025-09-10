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
lemma FactorsInDoubleFactorialMonotonic(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n + 1, p) >= FactorsInDoubleFactorial(n, p)
  decreases n
{
  if n == 0 {
    assert FactorsInDoubleFactorial(1, p) == FactorsInFactorial(1, p) - FactorsInDoubleFactorial(0, p);
    assert FactorsInDoubleFactorial(0, p) == 0;
    assert FactorsInDoubleFactorial(1, p) >= 0;
  }
}

lemma ComputeFactorsInDoubleFactorial(n: int, p: int, acc: int) returns (result: int)
  requires p > 1
  requires n >= 0
  ensures result == FactorsInDoubleFactorial(n, p)
{
  if n <= 0 {
    result := 0;
  } else if n % 2 == 1 {
    var prev := ComputeFactorsInDoubleFactorial(n - 1, p, 0);
    var factInFact := ComputeFactorsInFactorial(n, p);
    result := factInFact - prev;
  } else {
    var halfFactors := ComputeFactorsInFactorial(n / 2, p);
    result := halfFactors + (if p == 2 then n / 2 else 0);
  }
}

lemma ComputeFactorsInFactorial(n: int, p: int) returns (result: int)
  requires p > 1
  requires n >= 0
  ensures result == FactorsInFactorial(n, p)
{
  if n == 0 {
    result := 0;
  } else {
    var prev := ComputeFactorsInFactorial(n / p, p);
    result := n / p + prev;
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
  var factors2 := 0;
  var factors5 := 0;
  
  if N <= 0 {
    factors2 := 0;
    factors5 := 0;
  } else if N % 2 == 1 {
    // For odd N: FactorsInDoubleFactorial(N, p) = FactorsInFactorial(N, p) - FactorsInDoubleFactorial(N - 1, p)
    var factInFact2 := ComputeFactorsInFactorial(N, 2);
    var factInFact5 := ComputeFactorsInFactorial(N, 5);
    var prev2 := ComputeFactorsInDoubleFactorial(N - 1, 2, 0);
    var prev5 := ComputeFactorsInDoubleFactorial(N - 1, 5, 0);
    factors2 := factInFact2 - prev2;
    factors5 := factInFact5 - prev5;
  } else {
    // For even N: FactorsInDoubleFactorial(N, p) = FactorsInFactorial(N / 2, p) + (if p == 2 then N / 2 else 0)
    var halfFactors2 := ComputeFactorsInFactorial(N / 2, 2);
    var halfFactors5 := ComputeFactorsInFactorial(N / 2, 5);
    factors2 := halfFactors2 + N / 2;
    factors5 := halfFactors5;
  }
  
  if factors2 < factors5 {
    result := factors2;
  } else {
    result := factors5;
  }
}
// </vc-code>

