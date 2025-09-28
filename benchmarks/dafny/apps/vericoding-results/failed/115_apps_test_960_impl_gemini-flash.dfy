// <vc-preamble>
predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected while loop condition to `r <= k` */
function FindMinX(n: int, k: int): int
  requires n >= 1 && k >= 2
  ensures var res := FindMinX(n, k); res > 0 && (res / k) * (res % k) == n
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> res <= x
{
  var current_min_x := k * n + n + 1; // An initial large upper bound

  var r := 1;
  while r <= k // Corrected loop condition
    invariant 1 <= r <= k + 1
    invariant forall r' :: 1 <= r' < r && n % r' == 0 && (n / r') * k + r' > 0 ==> current_min_x <= (n / r') * k + r'
    invariant current_min_x > 0
  {
    if r > k { break; } // Added break to prevent r from exceeding k in the loop body

    if n % r == 0 {
      var q := n / r;
      var x := q * k + r;
      if x > 0 && (x / k) == q && (x % k) == r {
        if x < current_min_x {
          current_min_x := x;
        }
      }
    }
    r := r + 1;
  }

  return current_min_x;
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
/* code modified by LLM (iteration 5): no change needed, previous change was correct */
{
  result := FindMinX(n, k);
}
// </vc-code>
