

// <vc-helpers>
lemma lemma_divisors_correct(n: int, d: int)
  requires n >= 2
  requires 2 <= d <= n-1
  ensures (exists j :: 2 <= j <= d && n % j == 0) || (forall i :: 2 <= i <= d ==> n % i != 0)
  decreases d - 1
{
  if d == 2 {
    // Base case: either 2 divides n or it doesn't
  } else {
    lemma_divisors_correct(n, d-1);
    // The recursive call tells us about divisors up to d-1
  }
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
  var d := 2;
  while d < k
    invariant 2 <= d <= k
    invariant forall i :: 2 <= i < d ==> k % i != 0
    decreases k - d
  {
    if k % d == 0 {
      return false;
    }
    d := d + 1;
  }
  return true;
}
// </vc-code>

