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
    decreases m - d
  {
    if m % d == 0 {
      if (exists j :: 2 <= j < d && d % j == 0) {
        var j :| 2 <= j < d && d % j == 0;
        assert d == j * (d / j);
        assert m == d * (m / d);
        assert m == j * ((d / j) * (m / d));
        assert m % j == 0;
        assert false;
      }
      assert forall i :: 2 <= i < d ==> d % i != 0;
      largest := d;
      while m % d == 0
        invariant 1 <= m <= n
        invariant forall i :: 2 <= i < d ==> m % i != 0
        decreases m
      {
        var oldm := m;
        m := m / d;
        assert 1 <= m <= n;
        if (exists i :: 2 <= i < d && m % i == 0) {
          var i :| 2 <= i < d && m % i == 0;
          assert oldm == d * (oldm / d);
          assert oldm == d * m;
          assert oldm % i == 0;
          assert false;
        }
        assert forall i :: 2 <= i < d ==> m % i != 0;
      }
    } else {
      d := d + 1;
    }
  }
  if m > 1 {
    if (exists i :: 2 <= i < m && m % i == 0) {
      var i :| 2 <= i < m && m % i == 0;
      if i < d {
        assert false;
      } else {
        var t := m / i;
        assert t >= 2;
        assert t <= m / d;
        assert m / d < d;
        assert t < d;
        assert 2 <= t < d;
        assert m % t == 0;
        assert false;
      }
    }
    assert forall i :: 2 <= i < m ==> m % i != 0;
    largest := m;
  }
  return largest;
}
// </vc-code>

