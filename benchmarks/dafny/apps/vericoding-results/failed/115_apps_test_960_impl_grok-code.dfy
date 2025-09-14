predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
// No changes needed
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
  var min_x := (n / 1) * k + 1;
  var r := 2;
  while r < k
  {
    if n % r == 0 {
      var x := (n / r) * k + r;
      if x < min_x {
        min_x := x;
      }
    }
    r := r + 1;
  }
  result := min_x;
}
// </vc-code>

