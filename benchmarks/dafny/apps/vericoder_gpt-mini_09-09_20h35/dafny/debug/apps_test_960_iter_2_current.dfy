predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
// No additional helpers required for this proof.
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
  // Re-establish the loop invariant at exit point (r == k).
  assert sel == 0 <==> (forall t :: 1 <= t < r ==> n % t != 0);
  // 1 divides any integer, and k >= 2 by precondition, so 1 < r.
  assert n % 1 == 0;
  assert 1 < k;
  assert 1 < r;
  // Hence there exists a t in [1, r) dividing n (take t = 1).
  assert exists t :: 1 <= t < r && n % t == 0;
  // Therefore not all t in [1, r) fail to divide n, so sel != 0.
  assert !(forall t :: 1 <= t < r ==> n % t != 0);
  assert sel != 0;

  result := best;
  assert result > 0;

  // Show that result satisfies the constraint and is minimal.
  assert 1 <= sel < k;
  var q := n / sel;
  assert result == q * k + sel;
  assert result / k == q;
  assert result % k == sel;
  assert (result / k) * (result % k) == q * sel;
  assert q * sel == n;
}
// </vc-code>

