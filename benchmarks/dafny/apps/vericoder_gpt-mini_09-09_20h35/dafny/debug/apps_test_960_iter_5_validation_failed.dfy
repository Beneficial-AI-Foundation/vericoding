predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
lemma DivisorFromX(n: int, k: int, x: int)
  requires n >= 1 && k >= 2 && x > 0 && (x / k) * (x % k) == n
  ensures 1 <= x % k < k
  ensures n % (x % k) == 0
  ensures n / (x % k) == x / k
  ensures x == (n / (x % k)) * k + (x % k)
{
  // Standard div/mod decomposition
  assert x == (x / k) * k + x % k;
  assert 0 <= x % k < k;

  // If x % k == 0 then (x / k) * (x % k) == 0, so n == 0, contradicting n >= 1.
  // Therefore x % k != 0.
  assert (x % k == 0) ==> (x / k) * (x % k) == 0;
  assert (x / k) * (x % k) == n;
  assert n != 0;
  assert x % k != 0;
  assert 1 <= x % k < k;

  // From n == (x/k)*(x%k) we get that x%k divides n, and n/(x%k) == x/k.
  assert n == (x / k) * (x % k);
  assert n % (x % k) == 0;
  assert n / (x % k) == x / k;

  // Reconstruct x as (n / (x%k)) * k + (x%k).
  assert x == (n / (x % k)) * k + (x % k);
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
  var sel := 0;
  var best := 0;
  var r := 1;
  while r < k
    invariant 1 <= r <= k
    invariant sel == 0 <==> (forall t :: 1 <= t < r ==> n % t != 0)
    invariant sel != 0 ==> 1 <= sel < r && n % sel == 0 && best == (n / sel) * k + sel
    invariant sel != 0 ==> best > 0
    invariant sel != 0 ==> forall t :: 1 <= t < r && n % t == 0 ==> best <= (n / t) * k + t
    decreases k - r
  {
    if n % r == 0 {
      var x := (n / r) * k + r;
      if sel == 0 || x < best {
        best := x;
        sel := r;
      }
    }
    r := r + 1;
  }

  // There is always at least the divisor 1, so sel != 0 here.
  assert r == k;
  assert sel == 0 <==> (forall t :: 1 <= t < r ==> n % t != 0);
  assert n % 1 == 0;
  assert 1 < k;
  assert 1 < r;
  assert exists t :: 1 <= t < r && n % t == 0;
  assert !(forall t :: 1 <= t < r ==> n % t != 0);
  assert sel != 0;

  result := best;
  assert result > 0;

  // Establish representation of result via sel.
  assert 1 <= sel < k;
  var q := n / sel;
  assert result == q * k + sel;
  assert result / k == q;
  assert result % k == sel;
  assert (result / k) * (result % k) == q * sel;
  assert q * sel == n;

  // Prove minimality: for every x satisfying the constraint, result <= x.
  assert forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x by {
    // For arbitrary such x, assume its property and extract its divisor t = x % k.
    assume x > 0 && (x / k) * (x % k) == n;
    DivisorFromX(n, k, x);
    var t := x % k;
    // From the lemma: 1 <= t < k and n % t == 0 and n / t == x / k and x == (n / t) * k + t.
    assert 1 <= t < k;
    assert n % t == 0;
    assert x == (n / t) * k + t;

    // r == k, so 1 <= t < r.
    assert 1 <= t < r;

    // From loop invariant we have sel != 0 and thus best is <= candidate for any divisor < r.
    assert sel != 0;
    assert forall t0 :: 1 <= t0 < r && n % t0 == 0 ==> best <= (n / t0) * k + t0;
    assert best <= (n / t) * k + t;

    // result == best and candidate equals x, so result <= x.
    assert result == best;
    assert result <= x;
  }
}
// </vc-code>

