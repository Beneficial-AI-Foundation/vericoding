predicate ValidInput(n: int, m: int) {
    n >= 1 && m >= 2
}

function SocksAfterDay(n: int, m: int, day: int): int
  requires m > 0
{
    n + day / m - day
}

predicate CanWearSocksOnDay(n: int, m: int, day: int) 
  requires m > 0
{
    day >= 1 ==> SocksAfterDay(n, m, day - 1) > 0
}

// <vc-helpers>
lemma DivMulCancel(a: int, b: int)
  requires b > 0
  ensures (a * b) / b == a
{
  var q := (a * b) / b;
  var r := (a * b) % b;
  assert a * b == q * b + r;
  assert 0 <= r < b;
  assert b * (a - q) == r;
  if a - q != 0 {
    if a - q > 0 {
      // a - q >= 1
      assert a - q >= 1;
      // multiply both sides by b > 0
      assert b * (a - q) >= b * 1;
      assert b * 1 == b;
      assert b * (a - q) >= b;
      // but r == b*(a-q) and r < b, contradiction
      assert r >= b;
      assert false;
    } else {
      // a - q <= -1
      assert a - q <= -1;
      // multiply both sides by b > 0 preserves inequality direction
      assert b * (a - q) <= b * (-1);
      assert b * (-1) == -b;
      assert b * (a - q) <= -b;
      // but r == b*(a-q) and r >= 0, contradiction
      assert r <= -b;
      assert false;
    }
  }
  assert a - q == 0;
  assert q == a;
}

lemma SocksPositiveBeforeN(n: int, m: int, k: int)
  requires ValidInput(n, m)
  requires 1 <= k < n
  ensures SocksAfterDay(n, m, k) > 0
{
  // k/m >= 0 because k >= 1 and m > 0
  assert k / m >= 0;
  calc {
    SocksAfterDay(n, m, k);
    == { }
      n + k / m - k;
    >= { assert k / m >= 0; }
      n - k;
    >= { assert k < n; }
      1;
  }
}

lemma ExistsDayBound(n: int, m: int)
  requires ValidInput(n, m)
  ensures SocksAfterDay(n, m, n * m) <= 0
{
  // (n*m)/m == n because m > 0
  DivMulCancel(n, m);
  calc {
    SocksAfterDay(n, m, n * m);
    == { }
      n + (n * m) / m - n * m;
    == { }
      n + n - n * m;
    == { }
      2 * n - n * m;
    <= { assert n >= 1; assert m >= 2; }
      0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= n
  ensures result > 0
  ensures SocksAfterDay(n, m, result) <= 0
  ensures forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
// </vc-spec>
// <vc-code>
{
  var d := 1;
  // Use existence lemma to help establish an upper bound for the loop
  ExistsDayBound(n, m);
  while SocksAfterDay(n, m, d) > 0
    invariant 1 <= d <= n * m
    invariant forall k :: 1 <= k < d ==> SocksAfterDay(n, m, k) > 0
    decreases n * m - d
  {
    d := d + 1;
  }
  result := d;
  // prove result >= n by contradiction: if result < n then SocksAfterDay(...) > 0,
  // contradicting the loop exit condition SocksAfterDay(...) <= 0.
  if result < n {
    // result >= 1 by invariant, so we can apply the lemma
    SocksPositiveBeforeN(n, m, result);
    // from loop exit we know SocksAfterDay(n,m,result) <= 0
    assert SocksAfterDay(n, m, result) <= 0;
    // but lemma gives SocksAfterDay(n,m,result) > 0, contradiction
    assert false;
  }
  // result > 0 follows from invariant (d >= 1)
  assert result > 0;
  // forall k < result property follows from the loop invariant
  assert forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0;
}
// </vc-code>

