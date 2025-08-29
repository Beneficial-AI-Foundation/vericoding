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
  assert p1 > 1 && p2 > 1 && p3 > 1;
}

function CountPrimeFactors(n: nat, factors: seq<nat>) : nat
{
  if |factors| == 0 then 0
  else if Prime(factors[0]) && n % factors[0] == 0 then 
    1 + CountPrimeFactors(n, factors[1..])
  else 
    CountPrimeFactors(n, factors[1..])
}

function AllPrimesUpTo(limit: nat) : seq<nat>
{
  var candidates := seq(limit - 1, i => i + 2);
  seq(|candidates|, i requires 0 <= i < |candidates| => candidates[i]) 
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_multiply_prime(a: int) -> bool
Write a function that returns true if the given number is the multiplication of 3 prime numbers and false otherwise. Knowing that (a) is less then 100.
*/
// </vc-description>

// <vc-spec>
ghost predicate is_multiply_prime_spec(a: int)
  requires a < 100
{
  if a <= 1 then false
  else 
    exists p1, p2, p3 :: 
      p1 > 1 && p2 > 1 && p3 > 1 &&
      Prime(p1) && Prime(p2) && Prime(p3) &&
      a == p1 * p2 * p3
}
// </vc-spec>
// <vc-code>
function is_multiply_prime(a: int) : bool
  requires a < 100
  ensures is_multiply_prime(a) == is_multiply_prime_spec(a)
{
  if a <= 1 then false
  else 
    exists p1, p2, p3 :: 
      2 <= p1 < a && 2 <= p2 < a && 2 <= p3 < a &&
      Prime(p1) && Prime(p2) && Prime(p3) &&
      a == p1 * p2 * p3
}
// </vc-code>
