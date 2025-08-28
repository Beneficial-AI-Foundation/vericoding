//Problem 01

//problem02
//a)

// <vc-helpers>
lemma DivisionBound(n: int, d: int, q: int)
  requires n >= 0 && d > 0 && n >= d
  requires q * d <= n < (q + 1) * d
  ensures q <= n / 2 <==> d >= 2
{
  if d >= 2 {
    assert q * d <= n;
    assert q * 2 <= q * d;
    assert q * 2 <= n;
    assert q <= n / 2;
  }
}

lemma LoopTerminationHelps(n: int, d: int, q: int, r: int)
  requires n >= d && n >= 0 && d > 0
  requires d * q + r == n
  requires r >= 0 && q >= 0 && q <= n/2
  requires r >= d && q < n/2
  ensures r - d >= 0
  ensures q + 1 <= n/2
{
  assert r >= d;
  assert r - d >= 0;
  assert q < n/2;
  assert q + 1 <= n/2;
}

lemma PostconditionHelper(n: int, d: int, q: int, r: int)
  requires n >= d && n >= 0 && d > 0
  requires d * q + r == n
  requires r >= 0 && q >= 0 && q <= n/2
  requires !(r >= d && q < n/2)
  ensures 0 <= r < d
{
  if r >= d {
    assert !(q < n/2);
    assert q >= n/2;
    assert d * q >= d * (n/2);
    assert d * q + r >= d * (n/2) + d;
    assert n >= d * (n/2) + d;
    assert n >= d * (n/2 + 1);
    if d >= 2 {
      assert d * (n/2 + 1) >= 2 * (n/2 + 1);
      assert 2 * (n/2 + 1) == n + 2;
      assert n >= n + 2;
      assert false;
    } else {
      assert d == 1;
      assert n >= d;
      assert r >= d;
      assert r >= 1;
      assert r < d ==> false;
    }
  } else {
    assert r < d;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  q := 0;
  r := n;
  
  while r >= d && q < n/2
    invariant d * q + r == n
    invariant r >= 0
    invariant q >= 0
    invariant q <= n/2
    decreases r
  {
    LoopTerminationHelps(n, d, q, r);
    q := q + 1;
    r := r - d;
  }
  
  if r >= d {
    assert q >= n/2;
    assert d * q + r == n;
    assert r >= d;
    assert d * (n/2) + d <= n;
    assert d * ((n/2) + 1) <= n;
    assert d * (n/2 + 1) <= n;
    assert n >= d * (n/2 + 1);
    if d >= 2 {
      assert d * (n/2 + 1) >= 2 * (n/2 + 1);
      assert 2 * (n/2 + 1) == n + 2;
      assert n >= n + 2;
      assert false;
    } else {
      assert d == 1;
      assert false;
    }
  }
  
  PostconditionHelper(n, d, q, r);
}
// </vc-code>
