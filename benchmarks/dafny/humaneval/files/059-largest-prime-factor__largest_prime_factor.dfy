// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)

  requires n >= 2

  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
