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
lemma DivisorImpliesPrime(m: int, d: int)
  requires m >= 2
  requires 2 <= d <= m
  requires forall i :: 2 <= i < d ==> m % i != 0
  requires m % d == 0
  ensures forall i :: 2 <= i < d ==> d % i != 0
{
  if (exists j :: 2 <= j < d && d % j == 0) {
    var j :| 2 <= j < d && d % j == 0;
    // d = j * (d/j)
    assert d == j * (d / j);
    // m = d * (m/d)
    assert m == d * (m / d);
    // therefore m = j * ((d/j) * (m/d)), so j divides m
    assert m == j * ((d / j) * (m / d));
    assert m % j == 0;
    // contradicts the hypothesis that no i < d divides m
    assert false;
  }
  // if no such j exists, then no i in 2..d-1 divides d
}

lemma RemainingIsPrime(m: int, d: int)
  requires m >= 2
  requires forall i :: 2 <= i < d ==> m % i != 0
  requires d * d > m
  ensures forall i :: 2 <= i < m ==> m % i != 0
{
  if (exists i :: 2 <= i < m && m % i == 0) {
    var i :| 2 <= i < m && m % i == 0;
    if i < d {
      // contradicts the invariant directly
      assert false;
    } else {
      // i >= d, let t = m / i (the complementary factor)
      var t := m / i;
      // t >= 1 and since i < m we have t >= 2
      assert t >= 2;
      // from d*d > m we get m / d < d, hence t < d
      // because i >= d => m / i <= m / d < d
      assert t <= m / d;
      assert m / d < d;
      assert t < d;
      // t divides m (since m = i * t) and 2 <= t < d, contradicting the invariant
      assert false;
    }
  }
  // if no such divisor exists, m is prime (no i in 2..m-1 divides m)
}
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
      // d divides m and no smaller i divides m, so d is prime
      DivisorImpliesPrime(m, d);
      largest := d;
      // remove all factors d from m
      while m % d == 0
        invariant 1 <= m <= n
        invariant forall i :: 2 <= i < d ==> m % i != 0
        decreases m
      {
        m := m / d;
      }
    } else {
      d := d + 1;
    }
  }
  if m > 1 {
    // at loop exit d*d > m and no i < d divides m, so m is prime
    RemainingIsPrime(m, d);
    largest := m;
  }
  return largest;
}
// </vc-code>

