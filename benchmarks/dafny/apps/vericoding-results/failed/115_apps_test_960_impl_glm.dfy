predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>

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
  var min_x := n * k + 1;
  var best_r := 1;
  var r := 2;
  while r < k
      invariant 2 <= r <= k
      invariant min_x > 0
      invariant best_r in [1, r) && n % best_r == 0 && min_x == (n / best_r) * k + best_r
      invariant forall r0 :: 1 <= r0 < r && n % r0 == 0 ==> min_x <= (n / r0) * k + r0
  {
      if n % r == 0 {
          var x := (n / r) * k + r;
          if x < min_x {
              min_x := x;
              best_r := r;
          }
      }
      r := r + 1;
  }
  return min_x;
}
// </vc-code>

