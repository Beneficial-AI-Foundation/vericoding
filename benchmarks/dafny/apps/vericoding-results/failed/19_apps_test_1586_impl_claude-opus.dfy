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
lemma FactorsInFactorialDecreasesHelper(n: int, p: int)
  requires p > 1
  requires n > 0
  ensures n / p < n
{
  // Since p > 1 and n > 0, we have n/p < n
  // This is automatically proven by Dafny's arithmetic reasoning
}

lemma FactorsInFactorialTerminates(n: int, p: int)
  requires p > 1
  requires n >= 0
  decreases n
{
  if n > 0 {
    assert n / p < n by {
      FactorsInFactorialDecreasesHelper(n, p);
    }
    FactorsInFactorialTerminates(n / p, p);
  }
}

lemma FactorsInDoubleFactorialTerminates(n: int, p: int)
  requires p > 1
  requires n >= 0
  decreases n
{
  if n > 0 {
    if n % 2 == 1 {
      FactorsInDoubleFactorialTerminates(n - 1, p);
    } else {
      assert n / 2 < n;
      FactorsInFactorialTerminates(n / 2, p);
    }
  }
}

method ComputeFactorsInFactorial(n: int, p: int) returns (result: int)
  requires p > 1
  requires n >= 0
  ensures result == FactorsInFactorial(n, p)
  decreases n
{
  if n == 0 {
    result := 0;
  } else {
    FactorsInFactorialDecreasesHelper(n, p);
    var sub := ComputeFactorsInFactorial(n / p, p);
    result := n / p + sub;
  }
}

method ComputeFactorsInDoubleFactorial(n: int, p: int) returns (result: int)
  requires p > 1
  requires n >= 0
  ensures result == FactorsInDoubleFactorial(n, p)
  decreases n
{
  if n <= 0 {
    result := 0;
  } else if n % 2 == 1 {
    var factInFact := ComputeFactorsInFactorial(n, p);
    var prev := ComputeFactorsInDoubleFactorial(n - 1, p);
    result := factInFact - prev;
  } else {
    var halfFactors := ComputeFactorsInFactorial(n / 2, p);
    if p == 2 {
      result := halfFactors + n / 2;
    } else {
      result := halfFactors;
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
  var factors2 := 0;
  var factors5 := 0;
  
  if N <= 0 {
    factors2 := 0;
    factors5 := 0;
  } else {
    factors2 := ComputeFactorsInDoubleFactorial(N, 2);
    factors5 := ComputeFactorsInDoubleFactorial(N, 5);
  }
  
  if factors2 < factors5 {
    result := factors2;
  } else {
    result := factors5;
  }
}
// </vc-code>

