// <vc-preamble>
predicate ValidInput(N: int)
{
  N >= 1 && N <= 1000
}

predicate ValidOutput(result: int)
{
  result >= 0 && result < 1000000007
}

function Factorial(n: int): int
  requires n >= 0
{
  if n == 0 then 1 else n * Factorial(n-1)
}

function NumberOfDivisors(n: int): int
  requires n >= 1
{
  // Abstract function representing the count of positive divisors of n
  1 // Mathematical placeholder
}
// </vc-preamble>

// <vc-helpers>
lemma FactorialPositive(n: int)
  requires n >= 0
  ensures Factorial(n) >= 1
{
  if n == 0 {
    // Base case: 0! = 1
  } else {
    // Inductive case: n! = n * (n-1)! and both n >= 1 and (n-1)! >= 1
    FactorialPositive(n-1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var mod := 1000000007;

  // Count prime factors in N!
  var primeFactors := map[];

  if N >= 2 {
    for i := 2 to N 
      invariant forall p :: p in primeFactors ==> primeFactors[p] >= 1
    {
      var m := i;
      var j := 2;
      while j <= i && m > 1 
        invariant m >= 1
        invariant j >= 2
        invariant forall p :: p in primeFactors ==> primeFactors[p] >= 1
      {
        while m % j == 0 
          decreases m
          invariant m >= 1
          invariant j >= 2
          invariant forall p :: p in primeFactors ==> primeFactors[p] >= 1
        {
          if j in primeFactors {
            primeFactors := primeFactors[j := primeFactors[j] + 1];
          } else {
            primeFactors := primeFactors[j := 1];
          }
          m := m / j;
        }
        j := j + 1;
      }
    }
  }

  // Compute product of (count + 1) for each prime factor
  result := 1;
  var primes := [];
  var counts := [];

  // Extract keys and values from map
  if N >= 2 {
    for p := 2 to N 
      invariant forall i :: 0 <= i < |counts| ==> counts[i] >= 1
      invariant |primes| == |counts|
      invariant result >= 1
    {
      if p in primeFactors {
        primes := primes + [p];
        counts := counts + [primeFactors[p]];
      }
    }
  }

  // Calculate product
  if |counts| > 0 {
    for k := 0 to |counts| - 1 
      invariant result >= 0
      invariant result < mod
      invariant forall i :: 0 <= i < |counts| ==> counts[i] >= 1
    {
      assert counts[k] >= 1;
      assert counts[k] + 1 >= 2;
      result := (result * (counts[k] + 1)) % mod;
    }
  }
}
// </vc-code>
