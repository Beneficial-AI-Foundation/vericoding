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

  result := min_x;
}
// </vc-code>

