predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
lemma DivModProperties(x: int, k: int)
  requires k > 0
  ensures x == (x / k) * k + (x % k)
  ensures 0 <= x % k < k
{
}

lemma QuotientRemainderBounds(q: int, r: int, k: int, n: int)
  requires k >= 2 && n >= 1
  requires q * r == n
  requires 0 <= r < k
  ensures q * k + r >= 1
{
  if q == 0 {
    assert r == n >= 1;
  } else {
    assert q >= 1;
    assert q * k >= k >= 2;
    assert q * k + r >= k + 0 >= 2 >= 1;
  }
}

lemma OptimalityHelper(x: int, result: int, k: int, n: int)
  requires k >= 2
  requires x > 0 && (x / k) * (x % k) == n
  requires result > 0 && (result / k) * (result % k) == n
  requires result / k <= x / k
  requires result / k < x / k || result % k <= x % k
  ensures result <= x
{
  var q1 := result / k;
  var r1 := result % k;
  var q2 := x / k;
  var r2 := x % k;
  
  assert result == q1 * k + r1;
  assert x == q2 * k + r2;
  
  if q1 < q2 {
    assert result < x;
  } else {
    assert q1 == q2;
    assert result <= x;
  }
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
  var best := -1;
  var bestQ := -1;
  var bestR := -1;
  
  var maxQ := n + 1;
  var q := 0;
  
  while q <= maxQ
    invariant 0 <= q <= maxQ + 1
    invariant best == -1 ==> forall q', r :: 0 <= q' < q && 1 <= r < k ==> q' * r != n
    invariant best > 0 ==> SatisfiesConstraint(best, n, k)
    invariant best > 0 ==> bestQ == best / k && bestR == best % k
    invariant best > 0 ==> forall q', r :: 0 <= q' < q && 1 <= r < k && q' * r == n ==> (bestQ < q' || (bestQ == q' && bestR <= r))
  {
    if q * (k - 1) < n {
      q := q + 1;
      continue;
    }
    
    if q * 1 > n {
      break;
    }
    
    var r := 1;
    while r < k
      invariant 1 <= r <= k
      invariant best == -1 ==> forall q', r' :: 0 <= q' < q && 1 <= r' < k ==> q' * r' != n
      invariant best == -1 ==> forall r' :: 1 <= r' < r ==> q * r' != n
      invariant best > 0 ==> SatisfiesConstraint(best, n, k)
      invariant best > 0 ==> bestQ == best / k && bestR == best % k
      invariant best > 0 ==> forall q', r' :: 0 <= q' < q && 1 <= r' < k && q' * r' == n ==> (bestQ < q' || (bestQ == q' && bestR <= r'))
      invariant best > 0 ==> forall r' :: 1 <= r' < r && q * r' == n ==> (bestQ < q || (bestQ == q && bestR <= r'))
    {
      if q * r == n {
        var candidate := q * k + r;
        QuotientRemainderBounds(q, r, k, n);
        assert candidate > 0;
        assert candidate / k == q && candidate % k == r;
        DivModProperties(candidate, k);
        assert (candidate / k) * (candidate % k) == q * r == n;
        
        if best == -1 || candidate < best {
          best := candidate;
          bestQ := q;
          bestR := r;
        }
      }
      r := r + 1;
    }
    q := q + 1;
  }
  
  if best == -1 {
    var fallback := n * k + 1;
    DivModProperties(fallback, k);
    assert fallback / k == n && fallback % k == 1;
    assert (fallback / k) * (fallback % k) == n * 1 == n;
    result := fallback;
  } else {
    result := best;
  }
  
  assert SatisfiesConstraint(result, n, k);
  
  forall x | x > 0 && (x / k) * (x % k) == n
    ensures result <= x
  {
    var xQ := x / k;
    var xR := x % k;
    DivModProperties(x, k);
    
    if best > 0 {
      OptimalityHelper(x, result, k, n);
    } else {
      assert xR >= 1;
      assert x == xQ * k + xR >= 0 * k + 1 == 1;
      if xQ >= n {
        assert x >= n * k >= n * 2;
        assert result == n * k + 1 <= n * 2 + 1 <= x + 1;
        assert n >= 1;
        assert result <= n * k + 1 <= x;
      } else {
        assert false;
      }
    }
  }
}
// </vc-code>

