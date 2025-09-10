predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
lemma FactorizationExists(n: int, k: int)
  requires ValidInput(n, k)
  ensures exists x :: x > 0 && (x / k) * (x % k) == n
{
  // n = 1 * n, and since n >= 1, we have n > 0
  // If n < k, then x = k + n gives us x / k = 1 and x % k = n
  // So (x / k) * (x % k) = 1 * n = n
  if n < k {
    var x := k + n;
    assert x > 0;
    assert x / k == 1;
    assert x % k == n;
    assert (x / k) * (x % k) == n;
  } else {
    // n >= k >= 2, so we can use x = k + 1
    // x / k = 1, x % k = 1, so we need n = 1
    // Otherwise, we can factor n = q * r for some r < k
    var x := 2 * k + 1;  // This gives (2) * (1) = 2, works if n <= 2
    if n == 1 {
      var x := k + 1;
      assert x / k == 1;
      assert x % k == 1;
      assert (x / k) * (x % k) == 1 == n;
    } else {
      // For general case, use x = n * k + 1
      // This gives x / k = n and x % k = 1
      // So (x / k) * (x % k) = n * 1 = n
      var x := n * k + 1;
      assert x > 0;
      assert x / k == n;
      assert x % k == 1;
      assert (x / k) * (x % k) == n;
    }
  }
}

lemma DivModProperty(x: int, k: int, q: int, r: int)
  requires k > 0
  requires x == q * k + r
  requires 0 <= r < k
  ensures x / k == q
  ensures x % k == r
{
}

lemma VerifySolution(n: int, k: int, q: int, r: int)
  requires ValidInput(n, k)
  requires q > 0 && r > 0 && r < k
  requires q * r == n
  ensures var x := q * k + r; x > 0 && (x / k) * (x % k) == n
{
  var x := q * k + r;
  assert x > 0;
  DivModProperty(x, k, q, r);
  assert x / k == q;
  assert x % k == r;
  assert (x / k) * (x % k) == q * r == n;
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
  FactorizationExists(n, k);
  
  var minX := n * k + 1;  // Initial upper bound
  assert minX / k == n;
  assert minX % k == 1;
  assert (minX / k) * (minX % k) == n;
  
  var r := 1;
  while r < k
    invariant 1 <= r <= k
    invariant minX > 0
    invariant (minX / k) * (minX % k) == n
    invariant forall x :: x > 0 && (x / k) * (x % k) == n && 
                          exists rr :: 0 < rr < r && n % rr == 0 && rr < k && x == (n / rr) * k + rr
                          ==> minX <= x
  {
    if n % r == 0 {
      var q := n / r;
      if q > 0 {
        var x := q * k + r;
        VerifySolution(n, k, q, r);
        assert x > 0;
        assert (x / k) * (x % k) == n;
        
        if x < minX {
          minX := x;
        }
      }
    }
    r := r + 1;
  }
  
  return minX;
}
// </vc-code>

