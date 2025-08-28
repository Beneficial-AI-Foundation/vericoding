function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

// <vc-helpers>
lemma CPositive(n: nat)
  ensures C(n) > 0
  decreases n
{
  if n == 0 {
    assert C(0) == 1 > 0;
  } else {
    CPositive(n-1);
    assert C(n) == (4 * n - 2) * C(n-1) / (n + 1);
    assert 4 * n - 2 > 0;
    assert n + 1 > 0;
    assert C(n-1) > 0;
    assert (4 * n - 2) * C(n-1) > 0;
    assert C(n) > 0;
  }
}

lemma CDivisible(n: nat)
  ensures n == 0 || (n + 1) * C(n) == (4 * n - 2) * C(n-1)
  decreases n
{
  if n == 0 {
    assert C(0) == 1;
  } else {
    assert C(n) == (4 * n - 2) * C(n-1) / (n + 1);
    calc {
      (n + 1) * C(n);
      ==
      (n + 1) * ((4 * n - 2) * C(n-1) / (n + 1));
      ==
      (4 * n - 2) * C(n-1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method CalcCatalan(n: nat) returns (res: nat)
  ensures res == C(n)
{
  if n == 0 {
    res := 1;
  } else {
    var prev := CalcCatalan(n-1);
    var numerator := (4 * n - 2) * prev;
    res := numerator / (n + 1);
    assert n > 0;
    CDivisible(n);
    assert numerator == (4 * n - 2) * C(n-1);
    assert numerator == (n + 1) * C(n);
    assert res == C(n);
  }
}
// </vc-code>
