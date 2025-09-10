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
  
  // In integer division: (n * k + 1) / k = n when 1 < k
  assert x / k == n by {
    assert x == n * k + 1;
    assert 0 <= 1 < k;
    // Dafny knows (n * k + 1) / k = n when 0 <= 1 < k
  }
  
  assert x % k == 1 by {
    assert x == n * k + 1;
    assert 0 <= 1 < k;
    // Dafny knows (n * k + 1) % k = 1
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
  // These are Dafny's built-in properties of division and modulo
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
    assert x == q * k + r by {
      // This is the fundamental property of division and modulo
    }
    assert 0 <= r < k;
    assert q * r == n;
    
    if r == 0 {
      assert q * r == 0;
      assert n == 0;
      assert false;  // Contradicts n >= 1
    } else {
      assert 0 < r < k;
      assert q > 0 by {
        if q <= 0 {
          assert q * r <= 0;
          assert n <= 0;
          assert false; // Contradicts n >= 1
        }
      }
      assert n % r == 0 by {
        // q * r == n implies n is divisible by r
      }
      assert n / r == q by {
        // Since q * r == n and r > 0, we have n / r == q
      }
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
  assert minX > 0;
  
  // Prove the division and modulo properties directly
  assert minX / k == n by {
    assert minX == n * k + 1;
    assert 0 <= 1 < k;
  }
  
  assert minX % k == 1 by {
    assert minX == n * k + 1;
    assert 0 <= 1 < k;
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
  
  MinimalityLemma(n, k, minX);
  
  return minX;
}
// </vc-code>

