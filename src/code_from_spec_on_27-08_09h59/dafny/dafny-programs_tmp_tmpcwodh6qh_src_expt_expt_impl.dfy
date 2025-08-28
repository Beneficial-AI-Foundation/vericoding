ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma ExptPreservesInvariant(b: int, n: nat, i: nat)
  requires i <= n
  ensures Expt(b, n) == Expt(b, i) * Expt(b, n - i)
{
  if i == 0 {
    assert Expt(b, i) == 1;
    assert Expt(b, n - i) == Expt(b, n);
  } else if i == n {
    assert Expt(b, n - i) == 1;
    assert Expt(b, i) == Expt(b, n);
  } else {
    ExptPreservesInvariant(b, n, i - 1);
    assert Expt(b, n) == Expt(b, i - 1) * Expt(b, n - (i - 1));
    assert Expt(b, n) == Expt(b, i - 1) * Expt(b, n - i + 1);
    assert Expt(b, n - i + 1) == b * Expt(b, n - i);
    assert Expt(b, i) == b * Expt(b, i - 1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
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
