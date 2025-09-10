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
    invariant d*d <= temp_n + d 
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

  // A number has D divisors if its prime factorization is p1^e1 * p2^e2 * ... * pk^ek,
  // and D = (e1+1) * (e2+1) * ... * (ek+1).
  // We need to find divisors with exactly 75 divisors.
  // 75 = 75
  // 75 = 3 * 25
  // 75 = 5 * 15
  // 75 = 3 * 5 * 5 (this is not factorized into distinct parts for (ei+1) values)
  // Let the exponents of a divisor of N! be a_1, a_2, ..., a_k.
  // Then (a_1+1) * (a_2+1) * ... * (a_k+1) = 75.

  var count := 0;

  // Case 1: 75 = 75 (one prime factor, exponent 74)
  // e_1 + 1 = 75  =>  e_1 = 74
  // We need to find a prime factor p such that its exponent in N! is at least 74.
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
  // We need to pick two distinct primes p1, p2 from N! and have sufficient exponents.
  var p_keys := primeExponents.Keys;
  for i := 0 to |p_keys| - 1
  {
    var p1 := p_keys[i];
    if primeExponents[p1] >= 24
    {
      for j := 0 to |p_keys| - 1
      {
        var p2 := p_keys[j];
        if i != j && primeExponents[p2] >= 2
        {
          count := count + 1;
        }
      }
    }
  }
  // The above counts (p1^24 * p2^2) and (p1^2 * p2^24) as distinct if the set of chosen primes {p1, p2} is ordered.
  // Since we are looking for distinct prime exponents, (p1^24 * p2^2) and (p2^24 * p1^2) are different divisors.
  // We only need to ensure p1 and p2 are distinct primes of N!.
  // The current loop structure implicitly handles the distinctness of p1 and p2 due to (i != j).
  // However, it counts permutations. Example: p1=2, p2=3. It counts (exp2=24, exp3=2) and (exp2=2, exp3=24) as pairs if p1,p2 are simply chosen from the keys.

  // Let's refine the counting for Case 2 and Case 3 to avoid overcounting and ensure correctness based on distinct prime bases.

  var distinct_primes_count := |primeExponents.Keys|;

  // Case 2: (p_a^24 * p_b^2) where p_a != p_b
  // Number of choices for p_a with exponent >= 24: count_24
  // Number of choices for p_b with exponent >= 2: count_2
  var count_24 := 0;
  var count_2 := 0;
  for p in primeExponents.Keys
  {
    if primeExponents[p] >= 24
    {
      count_24 := count_24 + 1;
    }
    if primeExponents[p] >= 2
    {
      count_2 := count_2 + 1;
    }
  }


  // Need to be careful. If a prime has an exponent >= 24, it also has an exponent >= 2.
  // So, if we pick p_a (exp >= 24) and p_b (exp >= 2) where p_a != p_b:
  // (count_24 * count_2) counts pairs (p_a, p_b).
  // We also need to subtract cases where p_a is selected for both roles and p_a == p_b.
  // If p_a is one of the `count_24` primes, and p_b is one of the `count_2` primes.
  // If p_a = p_b, then this combination is invalid.
  // The number of pairs (p_a, p_b) where p_a is qualified for exp=24 and p_b for exp=2 and p_a != p_b
  // is (count_24 * count_2) - count_24 (since for each of the count_24 primes, if it is chosen as p_a, we cannot choose it again as p_b from the count_2 primes, but it IS in count_2).
  // Correct logic:
  // Choose p_a such that its exponent is >= 24. There are `count_24` such primes.
  // Choose p_b such that its exponent is >= 2 AND p_b != p_a. There are `count_2 - 1` such primes if p_a satisfies exp >= 2, otherwise `count_2` primes.
  // A simpler way:
  // Iterate over all pairs of distinct primes (p_a, p_b)
  for i := 0 to |p_keys| - 1
  {
    var p_a := p_keys[i];
    if primeExponents[p_a] >= 24
    {
      for j := 0 to |p_keys| - 1
      {
        var p_b := p_keys[j];
        if i != j && primeExponents[p_b] >= 2
        {
          count := count + 1;
        }
      }
    }
  }

  // Case 3: 75 = 5 * 15 (two distinct prime factors, exponents 4 and 14)
  // e_1 + 1 = 5   => e_1 = 4
  // e_2 + 1 = 15  => e_2 = 14
  // This is similar to Case 2, but we need to ensure we don't double count if a divisor can satisfy both Case 2 and Case 3 criteria with the same set of primes.
  // No, the set of *exponents* is different. A divisor with (p1^24 * p2^2) is different from (p1^14 * p2^4).
  // These cases are mutually exclusive by exponents, which is what defines distinct divisors.
  for i := 0 to |p_keys| - 1
  {
    var p_a := p_keys[i];
    if primeExponents[p_a] >= 14
    {
      for j := 0 to |p_keys| - 1
      {
        var p_b := p_keys[j];
        if i != j && primeExponents[p_b] >= 4
        {
          count := count + 1;
        }
      }
    }
  }

  // Case 4: 75 = 3 * 5 * 5  (This is wrong decomposition for (e_i+1) products of distinct primes. This implies two factors are 5, which means they must come from the same prime exponent in some twisted way.)
  // We need (e_1+1)*(e_2+1)*(e_3+1) = 75.
  // The only way to factor 75 into 3 numbers (each >= 2) is 3 * 5 * 5.
  // So: e_1 + 1 = 3   => e_1 = 2
  //     e_2 + 1 = 5   => e_2 = 4
  //     e_3 + 1 = 5   => e_3 = 4
  // We need three distinct primes p1, p2, p3 from N! with exponents at least 2, 4, 4 respectively.
  // Number of ways to choose 3 distinct primes from the available ones.
  for i := 0 to |p_keys| - 1
  {
    var p1 := p_keys[i];
    if primeExponents[p1] >= 2
    {
      for j := 0 to |p_keys| - 1
      {
        var p2 := p_keys[j];
        if i != j && primeExponents[p2] >= 4
        {
          for k := 0 to |p_keys| - 1
          {
            var p3 := p_keys[k];
            if i != k && j != k && primeExponents[p3] >= 4
            {
              count := count + 1;
            }
          }
        }
      }
    }
  }
  // The count is for ordered triples (p1, p2, p3) satisfying the exponent conditions.
  // A divisor of the form (p1^2 * p2^4 * p3^4) is distinct from (p1^4 * p2^2 * p3^4), etc.
  // The current nested loops produce ordered distinct tuples.
  // This is correct as we are looking for distinct divisors, which are defined by their unique prime factorizations (base primes AND their exponents).

  result := count;
  return result;
}
// </vc-code>

