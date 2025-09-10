predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
lemma MinimizeHelper(x: int, n: int, k: int, candidate: int)
  requires ValidInput(n, k)
  requires candidate > 0 && SatisfiesConstraint(candidate, n, k)
  requires forall x' :: 1 <= x' < candidate ==> !SatisfiesConstraint(x', n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> candidate <= x
{
}

lemma DivModProperties(k: int)
  requires k >= 2
  ensures forall x :: x > 0 ==> 0 <= x % k < k
  ensures forall x :: x > 0 ==> x == (x / k) * k + (x % k)
{
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
  DivModProperties(k);
  
  var r := 1;
  while r < k
    invariant 1 <= r <= k
  {
    if n % r == 0 {
      var d := n / r;
      var candidate := d * k + r;
      if candidate > 0 {
        assert (candidate / k) * (candidate % k) == d * r == n;
        MinimizeHelper(candidate, n, k, candidate);
        return candidate;
      }
    }
    r := r + 1;
  }
  
  // If we reach here, no valid r < k was found, use r = 0 case
  var candidate := n * k;
  assert (candidate / k) * (candidate % k) == n * 0 == 0;
  // But we need non-zero remainder, so this won't work
  // Let's try candidate = n * k + 1 instead
  candidate := n * k + 1;
  assert candidate > 0;
  assert candidate % k == 1;
  assert candidate / k == n;
  assert n * 1 == n;
  MinimizeHelper(candidate, n, k, candidate);
  return candidate;
}
// </vc-code>

