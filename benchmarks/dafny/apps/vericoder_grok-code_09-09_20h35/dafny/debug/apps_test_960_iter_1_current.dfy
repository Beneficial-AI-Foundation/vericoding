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
  var r := k - 1;
  var resultValue := -1;
  while r >= 1 
    invariant r >= 0
  {
    if n % r == 0 {
      resultValue := (n / r) * k + r;
      break;
    }
    r := r - 1;
  }
  result := resultValue;
}
// </vc-code>

