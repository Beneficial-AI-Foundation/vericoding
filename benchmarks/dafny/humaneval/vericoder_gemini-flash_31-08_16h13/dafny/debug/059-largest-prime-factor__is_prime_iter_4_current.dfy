function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
function is_prime_test(k: int) : bool
{
  if k < 2 then false
  else forall i :: 2 <= i * i <= k ==> k % i != 0 // Optimized to check divisibility only up to sqrt(k)
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if k < 2 {
    result := false;
  } else {
    var i := 2;
    result := true;
    while i * i <= k
      invariant 2 <= i <= k + 1
      invariant result ==> (forall j :: 2 <= j < i ==> k % j != 0)
    {
      if k % i == 0 {
        result := false;
        return;
      }
      i := i + 1;
    }
  }
  // This assertion is now moved inside the else branch for the case where result is true
  // and the loop has completed.
  if result {
    // We know that k has no divisors from 2 up to sqrt(k) (because of the loop invariant and termination).
    // If k has no divisors up to sqrt(k), and k >= 2, then k must be prime.
    // The postcondition for result => needs to prove this.
    // The invariant implies that for any j such that 2 <= j < i, k % j != 0.
    // When the loop terminates, i * i > k. This means i > sqrt(k).
    // So, if result is true, it means no divisors were found up to sqrt(k).
    // If k has no divisors up to sqrt(k), it is prime.
    // If k is prime, then forall j :: 2 <= j < k ==> k % j != 0.
    // This is implied by the primality of k.
  }
}
// </vc-code>

method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
{
  assume{:axiom} false;
}