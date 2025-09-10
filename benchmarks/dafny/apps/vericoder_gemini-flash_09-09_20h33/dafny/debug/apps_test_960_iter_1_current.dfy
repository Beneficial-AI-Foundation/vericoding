predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
function Modulo(x: int, k: int): int
  requires k > 0
  ensures 0 <= Modulo(x, k) < k
{
  (x % k + k) % k
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result > 0
  ensures SatisfiesConstraint(result, n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x
// </vc-spec>
// <vc-code>
{
  var min_x := -1;

  // We are searching for x such that (x / k) * (x % k) == n
  // Let q = x / k and r = x % k.
  // Then x = q*k + r, where 0 <= r < k.
  // The equation becomes q * r == n.
  // Since n >= 1, q and r must both be positive.
  // This implies 1 <= r < k and 1 <= q.

  // Iterate through possible values of r (remainder)
  // r must be a divisor of n AND 1 <= r < k
  // Also, q = n / r.
  // We want to minimize x = q*k + r = (n/r)*k + r.

  // The loop invariant ensures that if a solution exists for a remainder 'r_iter' less than current 'r',
  // it has already been considered and `min_x` has been updated accordingly if it's smaller.

  for r := 1 to k - 1
    invariant 1 <= r <= k
    invariant min_x == -1 || SatisfiesConstraint(min_x, n, k)
    invariant forall r_prime :: 1 <= r_prime < r && n % r_prime == 0 && r_prime < k && n / r_prime >= 0
      ==> (var x_prime := (n / r_prime) * k + r_prime;
          min_x != -1 && x_prime >= min_x)
  {
    if n % r == 0 {
      var q := n / r;
      // We need q >= 0, which is true because n >= 1 and r >= 1
      var x_candidate := q * k + r;

      if min_x == -1 || x_candidate < min_x {
        min_x := x_candidate;
      }
    }
  }

  // After the loop, min_x must contain the smallest x that satisfies the conditions.
  // This is because we iterated through all possible valid remainders r (1 <= r < k AAND r divides n)
  // and for each such r, we computed the corresponding quotient q = n/r, and thus x = q*k+r.
  // We took the minimum among all such x_candidates.

  // Proof that min_x is never -1 at the end:
  // Since n >= 1 and k >= 2 (from ValidInput), there must exist *some* x satisfying the conditions.
  // For example, if k divides n, take r=k-1, then q=n/(k-1) if n % (k-1) == 0. This is not guaranteed.
  // Consider the simple case where n = 1, k = 2.
  // We need (x/2)*(x%2) = 1.
  // r must be 1 (0 <= r < 2, so r could be 0 or 1. r cannot be 0 because n=1).
  // If r=1, then q * 1 = 1, so q=1.
  // x = q*k + r = 1*2 + 1 = 3.
  // In the loop, r=1. n%1==0. q=1/1=1. x_candidate = 1*2+1 = 3. min_x becomes 3.
  // So min_x will always be set to a valid positive number.

  result := min_x;
}
// </vc-code>

