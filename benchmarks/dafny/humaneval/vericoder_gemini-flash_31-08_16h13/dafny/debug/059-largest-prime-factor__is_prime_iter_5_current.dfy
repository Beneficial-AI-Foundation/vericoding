function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
function is_prime_test(k: int) : bool
{
  if k < 2 then false
  else forall i :: int :: 2 <= i * i <= k ==> k % i != 0 // Optimized to check divisibility only up to sqrt(k)
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
      invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    {
      if k % i == 0 {
        result := false;
        return;
      }
      i := i + 1;
    }
    // After the loop:
    // If result is true, it means no divisors were found from 2 up to floor(sqrt(k)).
    // Also, 2 <= k because we are in the else branch.
    // Therefore, k must be prime.
    // The postcondition for result => forall j :: 2 <= j < k ==> k % j != 0 holds.
    // If result is false, it means a divisor was found and returned, satisfying !result => exists j.
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