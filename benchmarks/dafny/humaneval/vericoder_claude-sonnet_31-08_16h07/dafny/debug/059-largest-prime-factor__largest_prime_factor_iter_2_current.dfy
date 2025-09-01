method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma DivisorExists(n: int)
  requires n >= 2
  ensures exists d :: 1 < d <= n && n % d == 0
{
  assert n % n == 0;
}

lemma SmallestDivisorIsPrime(n: int, d: int)
  requires n >= 2
  requires 1 < d <= n
  requires n % d == 0
  requires forall i :: 2 <= i < d ==> n % i != 0
  ensures is_prime_pred(d)
{
  // If d is the smallest divisor > 1, then d must be prime
  // because if d had a divisor k where 2 <= k < d, then k would also divide n
}

function FindSmallestDivisor(n: int): int
  requires n >= 2
  ensures 1 < FindSmallestDivisor(n) <= n
  ensures n % FindSmallestDivisor(n) == 0
  ensures is_prime_pred(FindSmallestDivisor(n))
{
  if n % 2 == 0 then 2
  else FindSmallestOddDivisor(n, 3)
}

function FindSmallestOddDivisor(n: int, candidate: int): int
  requires n >= 3 && n % 2 != 0
  requires candidate >= 3 && candidate % 2 == 1
  requires candidate <= n
  requires forall i :: 3 <= i < candidate && i % 2 == 1 ==> n % i != 0
  ensures 1 < FindSmallestOddDivisor(n, candidate) <= n
  ensures n % FindSmallestOddDivisor(n, candidate) == 0
  ensures is_prime_pred(FindSmallestOddDivisor(n, candidate))
  decreases n - candidate
{
  if candidate == n then 
    n
  else if n % candidate == 0 then 
    candidate
  else 
    FindSmallestOddDivisor(n, candidate + 2)
}

lemma PrimeFactorExists(n: int)
  requires n >= 2
  ensures exists p :: 1 < p <= n && n % p == 0 && is_prime_pred(p)
{
  DivisorExists(n);
  var d := FindSmallestDivisor(n);
  assert 1 < d <= n && n % d == 0;
  assert is_prime_pred(d);
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  PrimeFactorExists(n);
  var smallestPrime := FindSmallestDivisor(n);
  largest := smallestPrime;
  var current := n / smallestPrime;
  
  while current > 1
    invariant current >= 1
    invariant largest >= 1
    invariant is_prime_pred(largest)
    invariant largest <= n
    decreases current
  {
    var factor := FindSmallestDivisor(current);
    current := current / factor;
    if factor > largest {
      largest := factor;
    }
  }
}
// </vc-code>

