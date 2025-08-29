function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma PrimeFactorization(n: nat, p1: nat, p2: nat, p3: nat)
  requires n == p1 * p2 * p3
  requires Prime(p1) && Prime(p2) && Prime(p3)
  ensures n > 1
{
  assert p1 >= 2 && p2 >= 2 && p3 >= 2;
}

function CountPrimeFactors(n: nat, divisor: nat, count: nat): nat
  requires divisor >= 2
  decreases n
{
  if n <= 1 then count
  else if n % divisor == 0 && Prime(divisor) then
    CountPrimeFactors(n / divisor, 2, count + 1)
  else if divisor * divisor > n && n > 1 && Prime(n) then
    count + 1
  else if divisor < n then
    CountPrimeFactors(n, divisor + 1, count)
  else
    count
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_multiply_prime(a: int) -> bool
Write a function that returns true if the given number is the multiplication of 3 prime numbers and false otherwise. Knowing that (a) is less then 100.
*/
// </vc-description>

// <vc-spec>
function IsMultiplyPrime(a: int): bool
  requires a < 100
// </vc-spec>
// <vc-code>
{
  if a <= 1 then false
  else
    exists p1: nat, p2: nat, p3: nat ::
      Prime(p1) && Prime(p2) && Prime(p3) &&
      a == p1 * p2 * p3 &&
      p1 >= 2 && p2 >= 2 && p3 >= 2
}
// </vc-code>
