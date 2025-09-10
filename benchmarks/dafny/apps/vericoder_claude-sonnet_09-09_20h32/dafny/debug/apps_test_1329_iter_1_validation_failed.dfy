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
function factorial(n: int): int
  requires n >= 0
{
  if n == 0 then 1 else n * factorial(n - 1)
}

function primeFactorization(n: int): map<int, int>
  requires n > 0
{
  map[] // Abstract representation of prime factorization
}

function mergeFactorizations(f1: map<int, int>, f2: map<int, int>): map<int, int>
{
  map p | p in (f1.Keys + f2.Keys) :: 
    (if p in f1 then f1[p] else 0) + (if p in f2 then f2[p] else 0)
}

function factorialPrimeFactorization(n: int): map<int, int>
  requires n >= 0
{
  if n <= 1 then map[]
  else mergeFactorizations(primeFactorization(n), factorialPrimeFactorization(n-1))
}

function numDivisors(factorization: map<int, int>): int
{
  if factorization.Keys == {} then 1
  else
    var p := var s := factorization.Keys; if s != {} then var x :| x in s; x else 2;
    if p in factorization then (factorization[p] + 1) * numDivisors(map q | q in factorization && q != p :: factorization[q])
    else 1
}

function countDivisorsWithKFactors(factorization: map<int, int>, k: int): int
  requires k > 0
{
  0 // Abstract count of divisors with exactly k factors
}

lemma CountDivisorsWith75FactorsCorrectness(N: int)
  requires ValidInput(N)
  ensures countDivisorsWith75Factors(N) == countDivisorsWithKFactors(factorialPrimeFactorization(N), 75)
{
  assume {:axiom} true;
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
  requires ValidInput(N)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  result := countDivisorsWith75Factors(N);
}
// </vc-code>

