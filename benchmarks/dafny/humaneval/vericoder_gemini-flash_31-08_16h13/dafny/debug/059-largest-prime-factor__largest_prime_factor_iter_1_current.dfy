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
function method IsPrime(k: int): bool
  requires k >= 2 // Primality is defined for k >= 2
{
  forall i :: 2 <= i < k ==> k % i != 0
}

predicate IsFactor(f: int, n: int)
  requires n >= 1
  requires f >= 1
{
  n % f == 0
}

predicate IsLargestPrimeFactor(p: int, n: int)
  requires n >= 2 // n must be at least 2 for a prime factor to exist
  requires p >= 1
{
  (p == 1 && n == 1) || (p > 1 && IsPrime(p) && IsFactor(p, n) && forall k :: k > p && IsPrime(k) && IsFactor(k, n) ==> false)
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
  var current_n := n;
  var largest_found := 1;
  var d := 2;

  while d * d <= current_n
    invariant 2 <= d // current divisor candidate
    invariant current_n >= 1 // remaining part of n after division
    invariant n >= 2 // n is the original value, always >= 2
    invariant largest_found >= 1 // largest factor found so far
    invariant forall k :: k > largest_found && IsPrime(k) && IsFactor(k, n / current_n) ==> false // all prime factors of n/current_n are <= largest_found
    invariant n % current_n == 0 // n is divisible by current_n (or current_n is what remains after dividing n by previous factors)
    decreases current_n
  {
    if current_n % d == 0 {
      largest_found := d;
      current_n := current_n / d;
    } else {
      d := d + 1;
    }
  }

  // After the loop, if current_n > 1, it means current_n is a prime factor
  // (because all smaller factors d up to sqrt(current_n) have been checked)
  if current_n > 1 {
    largest_found := current_n;
  }

  largest := largest_found;
}
// </vc-code>

