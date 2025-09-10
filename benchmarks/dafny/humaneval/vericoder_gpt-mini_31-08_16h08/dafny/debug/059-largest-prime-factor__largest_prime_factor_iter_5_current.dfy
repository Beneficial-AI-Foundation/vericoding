method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
// No helpers needed for the fixed implementation.
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var m := n;
  largest := 1;
  var d := 2;
  while d * d <= m
    invariant 1 <= largest <= n
    invariant 1 <= m <= n
    invariant 2 <= d
    invariant forall i :: 2 <= i < d ==> m % i != 0
    decreases (m, n - d)
  {
    if is_prime_pred(d) && m % d == 0 {
      largest := d;
      assert is_prime_pred(largest);
      while m % d == 0
        invariant 1 <= m <= n
        invariant forall i :: 2 <= i < d ==> m % i != 0
        decreases m
      {
        m := m / d;
        assert 1 <= m <= n;
      }
    } else {
      d := d + 1;
    }
  }
  if m > 1 {
    // Prove m is prime: for any i with 2 <= i < m, m % i != 0
    assert forall i :: 2 <= i < d ==> m % i != 0;
    assert forall i :: d <= i < m ==> m % i != 0
    by {
      var i :| d <= i < m;
      if m % i == 0 {
        var k := m / i;
        // i >= d > 0, so k = m/i <= m/d
        assert k <= m / d;
        // loop exited so d*d > m, hence m / d < d
        assert m < d * d;
        assert m / d < d;
        assert k < d;
        assert 2 <= k;
        assert m % k == 0;
        // contradicts invariant forall i :: 2 <= i < d ==> m % i != 0
        assert false;
      }
    }
    largest := m;
    assert is_prime_pred(largest);
  }
  return largest;
}
// </vc-code>

