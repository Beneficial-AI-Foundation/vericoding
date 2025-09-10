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

lemma ConstructedNumberProperties(q: int, r: int, k: int)
  requires k > 0
  requires 0 < r < k
  requires q >= 0
  ensures var x := q * k + r; x > 0 && x / k == q && x % k == r
{
  var x := q * k + r;
  assert x > 0;
  DivModProperties(x, k);
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
        ConstructedNumberProperties(q, r, k);
        
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
    ConstructedNumberProperties(n, 1, k);
    result := fallback;
  } else {
    result := best;
  }
  
  forall x | x > 0 && (x / k) * (x % k) == n
    ensures result <= x
  {
    var xQ := x / k;
    var xR := x % k;
    DivModProperties(x, k);
    
    if best > 0 {
      assert xR >= 1;
      assert xQ * xR == n;
      if bestQ < xQ {
        assert result <= x;
      } else if bestQ == xQ {
        assert bestR <= xR;
        assert result <= x;
      } else {
        assert false;
      }
    } else {
      assert xR >= 1;
      assert xQ * xR == n;
      assert xQ >= n;
      assert x >= n * k + 1;
      assert result <= x;
    }
  }
}
// </vc-code>

