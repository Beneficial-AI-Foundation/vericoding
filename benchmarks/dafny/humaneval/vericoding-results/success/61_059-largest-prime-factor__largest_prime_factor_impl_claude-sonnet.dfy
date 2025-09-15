// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed division by zero error by adding precondition */
function is_factor(a: int, b: int): bool
  requires b > 0 && a != 0
{
  b % a == 0
}

function largest_factor_helper(n: int, candidate: int): int
  requires n >= 2 && 1 <= candidate <= n
  decreases candidate
{
  if candidate == 1 then 1
  else if is_factor(candidate, n) && is_prime_pred(candidate) then candidate
  else largest_factor_helper(n, candidate - 1)
}

lemma largest_factor_helper_bounds(n: int, candidate: int)
  requires n >= 2 && 1 <= candidate <= n
  ensures var result := largest_factor_helper(n, candidate); 1 <= result <= n
{
}

lemma largest_factor_helper_prime(n: int, candidate: int)
  requires n >= 2 && 1 <= candidate <= n
  ensures var result := largest_factor_helper(n, candidate); result == 1 || (result > 1 && is_prime_pred(result))
{
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)

  requires n >= 2

  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): same implementation */
{
  largest := largest_factor_helper(n, n);
  largest_factor_helper_bounds(n, n);
  largest_factor_helper_prime(n, n);
}
// </vc-code>
