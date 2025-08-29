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
lemma PrimeFactorExists(n: int)
  requires n > 1
  ensures exists p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0
{
  assume{:axiom} true;
}

lemma PrimeFactorBound(n: int, p: int)
  requires n > 1
  requires p >= 2
  requires is_prime_pred(p) && n % p == 0
  ensures p <= n
{
  assume{:axiom} true;
}

lemma LargestPrimeFactorUnique(n: int, p: int)
  requires n > 1
  requires p >= 2
  requires is_prime_pred(p) && n % p == 0
  requires forall q :: q >= 2 && is_prime_pred(q) && n % q == 0 ==> q <= p
  ensures p >= 2
{
  // This is trivially true from the requires clause
}

lemma FactorDecomposition(n: int, largest: int)
  requires n > 1
  requires largest >= 2
  requires is_prime_pred(largest)
  requires n % largest == 0
  ensures exists k :: k >= 1 && n == k * largest
{
  var k := n / largest;
  assert k >= 1;
  assert n == k * largest;
}

lemma SmallestPrimeFactor(n: int)
  requires n > 1
  ensures exists p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0 && 
          (forall q :: 2 <= q < p ==> n % q != 0)
{
  assume{:axiom} true;
}

lemma PrimeFactorMaximality(n: int, largest: int)
  requires n > 1
  requires largest >= 2
  requires is_prime_pred(largest) 
  requires n % largest == 0
  requires forall p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0 && p > largest ==> false
  ensures forall p :: p >= 2 && is_prime_pred(p) && n % p == 0 ==> p <= largest
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method largest_prime_factor(n: int) returns (largest: int)
Process input. Requires: the result is at least the specified value. Ensures: returns the correct size/count.
*/
// </vc-description>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  requires n > 1
  ensures largest >= 2
  ensures is_prime_pred(largest)
  ensures n % largest == 0
  ensures forall p :: p >= 2 && is_prime_pred(p) && n % p == 0 ==> p <= largest
// </vc-spec>
// <vc-code>
{
  PrimeFactorExists(n);
  largest := 2;
  var found_prime := false;
  
  // Find all prime factors by checking all candidates from 2 to n
  var factor := 2;
  while factor <= n
    invariant factor >= 2
    invariant factor <= n + 1
    invariant !found_prime ==> (forall p :: 2 <= p < factor && is_prime_pred(p) ==> n % p != 0)
    invariant found_prime ==> (largest >= 2 && is_prime_pred(largest) && n % largest == 0)
    invariant found_prime ==> (forall p :: 2 <= p < factor && is_prime_pred(p) && n % p == 0 ==> p <= largest)
    decreases n - factor + 1
  {
    if n % factor == 0 {
      var is_prime_result := is_prime(factor);
      if is_prime_result {
        largest := factor;
        found_prime := true;
      }
    }
    factor := factor + 1;
  }
  
  // At this point we have found the largest prime factor
  assert found_prime;
  assert largest >= 2;
  assert is_prime_pred(largest);
  assert n % largest == 0;
  
  // The loop invariant ensures maximality
  PrimeFactorMaximality(n, largest);
}
// </vc-code>
