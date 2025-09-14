ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma ExptMult(b: int, n: nat, m: nat)
  ensures Expt(b, n + m) == Expt(b, n) * Expt(b, m)
{
  if n == 0 {
    assert Expt(b, 0 + m) == Expt(b, m);
    assert Expt(b, 0) == 1;
    assert Expt(b, 0) * Expt(b, m) == 1 * Expt(b, m) == Expt(b, m);
  } else {
    ExptMult(b, n - 1, m);
    assert Expt(b, n + m) == b * Expt(b, (n - 1) + m);
    assert Expt(b, (n - 1) + m) == Expt(b, n - 1) * Expt(b, m);
    assert Expt(b, n + m) == b * Expt(b, n - 1) * Expt(b, m);
    assert Expt(b, n) == b * Expt(b, n - 1);
    assert Expt(b, n) * Expt(b, m) == b * Expt(b, n - 1) * Expt(b, m);
  }
}
// </vc-helpers>

// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// <vc-code>
{
  res := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res == Expt(b, i)
  {
    res := res * b;
    i := i + 1;
  }
}
// </vc-code>

