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

function CountPrimeFactors(n: nat, limit: nat): nat
  requires limit >= 2
  decreases limit
{
  if limit == 2 then
    if n >= 2 && Prime(2) && n % 2 == 0 then 1 else 0
  else
    CountPrimeFactors(n, limit - 1) + 
    (if n >= limit && Prime(limit) && n % limit == 0 then 1 else 0)
}

ghost function IsProductOfThreePrimes(n: nat): bool
  requires n < 100
{
  exists p1, p2, p3 :: 
    Prime(p1) && Prime(p2) && Prime(p3) && 
    p1 <= p2 <= p3 &&
    n == p1 * p2 * p3
}

function CheckAllTriples(n: nat, p1: nat, p2: nat, p3: nat): bool
  requires n < 100
  decreases 100 - p1, 100 - p2, 100 - p3
{
  if p1 > 97 then false
  else if p2 > 97 then CheckAllTriples(n, p1 + 1, 2, 2)
  else if p3 > 97 then CheckAllTriples(n, p1, p2 + 1, 2)
  else if Prime(p1) && Prime(p2) && Prime(p3) && p1 <= p2 <= p3 && n == p1 * p2 * p3 then true
  else CheckAllTriples(n, p1, p2, p3 + 1)
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
function IsMultiplyPrime(a: int): bool
  requires a < 100
{
  if a <= 1 then false
  else 
    var n := a as nat;
    CheckAllTriples(n, 2, 2, 2)
}
// </vc-code>
