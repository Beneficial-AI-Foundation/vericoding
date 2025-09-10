predicate ValidInput(N: int)
{
  1 <= N <= 100
}

function countDivisorsWith75Factors(N: int): int
  requires ValidInput(N)
{
  0 // Abstract specification - represents the count of divisors of N! that have exactly 75 divisors
}

predicate ValidOutput(result: int)
{
  result >= 0
}

// <vc-helpers>
function getPrimeFactors(n: int): map<int, int>
  requires n > 1
  ensures forall p | p in getPrimeFactors(n) :: Prime(p) && getPrimeFactors(n)[p] > 0
  ensures (forall p | Prime(p) :: p > n ==> !(p in getPrimeFactors(n)))
  ensures (n == (Product(p | p in getPrimeFactors(n) :: p.Pow(getPrimeFactors(n)[p]))))
{
  var factors: map<int, int> := map[];
  var temp_n := n;
  var d := 2;
  while temp_n > 1
    invariant d*d <= temp_n + d || temp_n < d
    invariant (n == (Product(p | p in factors :: p.Pow(factors[p])) * temp_n))
  {
    if temp_n % d == 0
    {
      factors := factors + map[d := factors.Get(d, 0) + 1];
      temp_n := temp_n / d;
    }
    else
    {
      d := d + 1;
    }
  }
  return factors;
}


function FactorialPrimeExponents(N: int, p: int): int
  requires N >= 0
  requires Prime(p)
  ensures FactorialPrimeExponents(N, p) >= 0
{
  if N == 0 then 0
  else N/p + FactorialPrimeExponents(N/p, p)
}

lemma FactorialPrimeExponents_property(N: int, p: int)
  requires N >= 0
  requires Prime(p)
  ensures FactorialPrimeExponents(N, p) == sum k: int | 1 <= k && p.Pow(k) <= N :: N/p.Pow(k)
{
  if N == 0 { }
  else {
    calc {
      FactorialPrimeExponents(N, p);
      N/p + FactorialPrimeExponents(N/p, p);
      { reveal FactorialPrimeExponents_property(N/p, p); }
      N/p + sum k: int | 1 <= k && p.Pow(k) <= N/p :: (N/p)/p.Pow(k);
      N/p + sum k: int | 1 <= k && p.Pow(k+1) <= N :: N/p.Pow(k+1);
      sum k: int | 1 <= k && p.Pow(k) <= N :: N/p.Pow(k);
    }
  }
}

function PrimesUpTo(N: int): seq<int>
  requires N >= 2
  reads globals
  ensures forall p | p in PrimesUpTo(N) :: Prime(p) && p <= N
  ensures forall p | Prime(p) && p <= N :: p in PrimesUpTo(N)
{
  var primes: seq<int> := [];
  for i := 2 to N
  {
    if Prime(i)
    {
      primes := primes + [i];
    }
  }
  return primes;
}

predicate Prime(x: int)
{
  x >= 2 && forall d: int | 2 <= d < x :: x % d != 0
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var primeExponents: map<int, int> := map[];
  for p in PrimesUpTo(N)
  {
    primeExponents := primeExponents + map[p := FactorialPrimeExponents(N, p)];
  }

  var count := 0;

  // Case 1: 75 = 75 (one prime factor, exponent 74)
  // e_1 + 1 = 75  =>  e_1 = 74
  for p in primeExponents.Keys
  {
    if primeExponents[p] >= 74
    {
      count := count + 1;
    }
  }

  // Case 2: 75 = 3 * 25 (two distinct prime factors, exponents 2 and 24)
  // e_1 + 1 = 3   => e_1 = 2
  // e_2 + 1 = 25  => e_2 = 24
  var keys := primeExponents.Keys;
  for i := 0 to |keys| - 1
  {
    var p1 := keys[i];
    if primeExponents[p1] >= 24
    {
      for j := 0 to |keys| - 1
      {
        var p2 := keys[j];
        if i != j && primeExponents[p2] >= 2
        {
          count := count + 1;
        }
      }
    }
  }

  // Case 3: 75 = 5 * 15 (two distinct prime factors, exponents 4 and 14)
  // e_1 + 1 = 5   => e_1 = 4
  // e_2 + 1 = 15  => e_2 = 14
  for i := 0 to |keys| - 1
  {
    var p1 := keys[i];
    if primeExponents[p1] >= 14
    {
      for j := 0 to |keys| - 1
      {
        var p2 := keys[j];
        if i != j && primeExponents[p2] >= 4
        {
          count := count + 1;
        }
      }
    }
  }

  // Case 4: 75 = 3 * 5 * 5 (three distinct prime factors, exponents 2, 4, 4)
  // e_1 + 1 = 3   => e_1 = 2
  // e_2 + 1 = 5   => e_2 = 4
  // e_3 + 1 = 5   => e_3 = 4
  for i := 0 to |keys| - 1
  {
    var p1 := keys[i];
    if primeExponents[p1] >= 2
    {
      for j := 0 to |keys| - 1
      {
        var p2 := keys[j];
        if i != j && primeExponents[p2] >= 4
        {
          for k := 0 to |keys| - 1
          {
            var p3 := keys[k];
            if i != k && j != k && primeExponents[p3] >= 4
            {
              count := count + 1;
            }
          }
        }
      }
    }
  }

  result := count;
  return result;
}
// </vc-code>

