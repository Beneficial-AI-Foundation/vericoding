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
  var x := n * k + 1;
  assert x > 0;
  assert x == n * k + 1;
  
  // Fix: Correct division calculation
  calc == {
    x / k;
    (n * k + 1) / k;
    n + (1 / k);  // Since 1 < k, this is n + 0
    n;
  }
  
  calc == {
    x % k;
    (n * k + 1) % k;
    1;
  }
  
  assert (x / k) * (x % k) == n * 1 == n;
}

lemma DivModProperty(x: int, k: int, q: int, r: int)
  requires k > 0
  requires x == q * k + r
  requires 0 <= r < k
  ensures x / k == q
  ensures x % k == r
{
  // Dafny's built-in division and modulo properties
  assert x / k == (q * k + r) / k == q + r / k == q;
  assert x % k == (q * k + r) % k == r;
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

lemma MinimalityLemma(n: int, k: int, minX: int)
  requires ValidInput(n, k)
  requires minX > 0
  requires (minX / k) * (minX % k) == n
  requires forall r :: 0 < r < k && n % r == 0 ==> 
            (var q := n / r; var x := q * k + r; minX <= x)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> minX <= x
{
  forall x | x > 0 && (x / k) * (x % k) == n
    ensures minX <= x
  {
    var q := x / k;
    var r := x % k;
    assert x == q * k + r;
    assert 0 <= r < k;
    assert q * r == n;
    
    if r == 0 {
      assert q * r == q * 0 == 0;
      assert n == 0;
      assert false;  // Contradicts n >= 1
    } else {
      assert 0 < r < k;
      assert q > 0 by {
        assert q * r == n;
        assert r > 0;
        assert n >= 1;
      }
      assert n % r == 0 by {
        assert q * r == n;
      }
      assert n / r == q;
      var x2 := q * k + r;
      assert x2 == x;
      assert minX <= x2;
      assert minX <= x;
    }
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
  FactorizationExists(n, k);
  
  var minX := n * k + 1;
  assert minX == n * k + 1;
  assert minX > 0;
  
  // Use calculation to prove division
  calc == {
    minX / k;
    (n * k + 1) / k;
    n;
  }
  
  calc == {
    minX % k;
    (n * k + 1) % k;
    1;
  }
  
  assert (minX / k) * (minX % k) == n * 1 == n;
  
  var r := 1;
  while r < k
    invariant 1 <= r <= k
    invariant minX > 0
    invariant (minX / k) * (minX % k) == n
    invariant forall rr :: 0 < rr < r && n % rr == 0 ==> 
              (var q := n / rr; var x := q * k + rr; minX <= x)
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
  
  assert r == k;
  assert forall rr :: 0 < rr < k && n % rr == 0 ==> 
         (var q := n / rr; var x := q * k + rr; minX <= x);
  
  MinimalityLemma(n, k, minX);
  assert forall x :: x > 0 && (x / k) * (x % k) == n ==> minX <= x;
  
  return minX;
}
// </vc-code>

