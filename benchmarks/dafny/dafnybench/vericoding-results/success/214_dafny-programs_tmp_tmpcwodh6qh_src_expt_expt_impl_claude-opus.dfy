ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma ExptAddition(b: int, n1: nat, n2: nat)
  ensures Expt(b, n1 + n2) == Expt(b, n1) * Expt(b, n2)
{
  if n1 == 0 {
    assert Expt(b, 0 + n2) == Expt(b, n2);
    assert Expt(b, 0) * Expt(b, n2) == 1 * Expt(b, n2) == Expt(b, n2);
  } else {
    calc {
      Expt(b, n1 + n2);
      == b * Expt(b, (n1 - 1) + n2);
      == { ExptAddition(b, n1 - 1, n2); }
      b * (Expt(b, n1 - 1) * Expt(b, n2));
      == (b * Expt(b, n1 - 1)) * Expt(b, n2);
      == Expt(b, n1) * Expt(b, n2);
    }
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

