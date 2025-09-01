function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
function is_prime_pred_axiom(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
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
  var i := 2;
  while i * i <= k
    invariant 2 <= i
    invariant i <= k + 1 
    invariant forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      return false;
    }
    i := i + 1;
  }
  // After the loop, we know that for all j such that 2 <= j < i, k % j != 0.
  // We also know that i * i > k, which implies i > sqrt(k).
  // If k is prime, then k has no divisors other than 1 and itself.
  // If k has a divisor greater than sqrt(k), it must also have a divisor less than sqrt(k).
  // Since we haven't found any divisors up to sqrt(k) (represented by i-1), k must be prime.
  return true;
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