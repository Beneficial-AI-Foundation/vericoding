function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>
lemma RMonotonic(n: nat)
  ensures forall m: nat :: m <= n ==> R(m) <= R(n)
{
  if n == 0 {
    return;
  }
  RMonotonic(n-1);
  if R(n-1) > n {
    assert R(n) == R(n-1) - n;
    assert R(n-1) >= n + 1;
    assert R(n) <= R(n-1);
    forall m: nat | m <= n-1
      ensures R(m) <= R(n)
    {
      assert R(m) <= R(n-1);
      assert R(n) <= R(n-1);
    }
  } else {
    assert R(n) == R(n-1) + n;
    assert R(n) >= R(n-1);
    forall m: nat | m <= n-1
      ensures R(m) <= R(n)
    {
      assert R(m) <= R(n-1);
      assert R(n-1) <= R(n);
    }
  }
  assert R(n) <= R(n);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method CalcR(n: nat) returns (r: nat)
  ensures r == R(n)
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == R(i)
  {
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
}
// </vc-code>
