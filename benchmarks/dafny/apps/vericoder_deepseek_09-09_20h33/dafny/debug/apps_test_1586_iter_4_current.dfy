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
    FactorsInDoubleFactorialTermination(n - 1, p);
  } else {
    FactorsInDoubleFactorialTermination(n / 2, p);
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
    // Show that recursive call decreases the measure
    FactorialVsDoubleFactorial(n - 1, p);
    // Postcondition from recursive call gives us the inequality for n-1 case
  } else {
    // Show that recursive call decreases the measure  
    FactorialVsDoubleFactorial(n / 2, p);
    // Postcondition from recursive call gives us the inequality for n/2 case
  }
  
  // The actual proof of the inequality comes from the function definitions
  // which are already verified to be consistent via their ensures clauses
}

lemma FactorsInDoubleFactorialDecreases(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures FactorsInDoubleFactorial(n, p) >= 0
  decreases n
{
  if n <= 0 {
    return;
  }
  if n % 2 == 1 {
    FactorsInDoubleFactorialDecreases(n - 1, p);
  } else {
    FactorsInDoubleFactorialDecreases(n / 2, p);
  }
}

// Helper lemma to establish key relationship properties
lemma DoubleFactorialProperties(n: int, p: int)
  requires p > 1
  requires n >= 0
  ensures n % 2 == 1 ==> FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n, p) - FactorsInDoubleFactorial(n - 1, p)
  ensures n % 2 == 0 ==> FactorsInDoubleFactorial(n, p) == FactorsInFactorial(n / 2, p) + (if p == 2 then n / 2 else 0)
  decreases n
{
  // This lemma is essentially just stating the postconditions again
  // but helps Dafny's proof automation by making the properties explicit
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidResult(N, result)
// </vc-spec>
// <vc-code>
{
  // Verify termination guarantee for both cases
  FactorsInDoubleFactorialDecreases(N, 2);
  FactorsInDoubleFactorialDecreases(N, 5);
  
  // Call the helper lemma to establish key properties for verification
  DoubleFactorialProperties(N, 2);
  DoubleFactorialProperties(N, 5);
  
  var count2 := FactorsInDoubleFactorial(N, 2);
  var count5 := FactorsInDoubleFactorial(N, 5);
  
  if count2 < count5 {
    result := count2;
  } else {
    result := count5;
  }
}
// </vc-code>

