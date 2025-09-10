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

// Helper to prove k positive in SatisfiesConstraint
lemma LemmaSatisfiesConstraintKPositive(x: int, n: int, k: int)
  requires SatisfiesConstraint(x, n, k)
  ensures k > 0
{
  // The predicate SatisfiesConstraint already states k > 0
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
  var min_x := -1; // Represents the smallest x found so far that satisfies the constraint

  // Iterate over possible values of r (remainder), from 1 to k-1.
  // r must be greater than 0 since it is a remainder of division by k and k >= 2.
  // n = q * r where q is an integer. So r must be a divisor of n.
  for r := 1 to k - 1
    // Loop invariants to help with verification:
    invariant 1 <= r <= k // r is within the expected range [1, k-1], loop condition implies r <= k-1
    invariant min_x == -1 || SatisfiesConstraint(min_x, n, k)
    invariant min_x == -1 || min_x > 0 // min_x, if set, must be positive
    // This invariant ensures that any x_prime found for smaller r's that satisfy the divisibility
    // condition, if also satisfying the overall constraint, is greater than or equal to min_x.
    // This helps prove the postcondition forall x :: ... result <= x
    invariant forall r_prime :: (1 <= r_prime < r && n % r_prime == 0) ==>
                                (var x_prime := (n / r_prime) * k + r_prime;
                                 var q_prime := n / r_prime;
                                 x_prime > 0 && (x_prime / k) == q_prime && (x_prime % k) == r_prime && 
                                 (min_x == -1 || x_prime >= min_x))
  {
    // If r is a divisor of n, then we can find a corresponding q such that n = q * r.
    if n % r == 0 {
      var q := n / r; // Calculate q
      var x_candidate := q * k + r; // Calculate x_candidate based on q and r

      // Proof obligations for x_candidate:
      // Property: (x_candidate / k) * (x_candidate % k) == n
      // (q * k + r) / k = q (since 0 < r < k)
      // (q * k + r) % k = r (since 0 < r < k)
      // So, (q * k + r) / k * (q * k + r) % k = q * r = n
      // Also, x_candidate > 0 because q >= 0 (since n >= 1, r >= 1) and k >= 2, r >= 1.
      assert q >= 0; // n >= 1, r >= 1 => q = n/r >= 1
      assert x_candidate > 0;
      assert x_candidate / k == q;
      assert x_candidate % k == r;
      assert SatisfiesConstraint(x_candidate, n, k);

      // If this x_candidate is smaller than the current minimum, update min_x.
      if min_x == -1 || x_candidate < min_x {
        min_x := x_candidate;
      }
    }
  }

  // After the loop, min_x holds the smallest x found that satisfies the constraint.
  // The problem guarantees that such an x exists.
  // Thus, min_x will not be -1 at the end.
  assert min_x != -1;
  assert SatisfiesConstraint(min_x, n, k);
  assert min_x > 0;

  result := min_x;
}
// </vc-code>

