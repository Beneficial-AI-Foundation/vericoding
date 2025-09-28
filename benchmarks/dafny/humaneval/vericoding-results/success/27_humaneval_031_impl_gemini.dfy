// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause for termination */
function CheckNoDivisors(n: int, k: int): bool
  requires n > 1
  requires 2 <= k <= n + 1
  ensures CheckNoDivisors(n, k) <==> (forall i :: k <= i < n ==> n % i != 0)
  decreases n - k
{
  if k >= n then
    true
  else if n % k == 0 then
    false
  else
    CheckNoDivisors(n, k + 1)
}
// </vc-helpers>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): logic is correct, no changes needed */
  if n < 2 {
    result := false;
  } else {
    result := CheckNoDivisors(n, 2);
  }
}
// </vc-code>
