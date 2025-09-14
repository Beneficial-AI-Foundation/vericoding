ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma Expt_unfold(b: int, n: nat)
  requires n > 0
  ensures Expt(b, n) == b * Expt(b, n - 1)
{
  if n == 0 {
    // unreachable due to requires
  } else {
    assert Expt(b, n) == b * Expt(b, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// <vc-code>
{
  var i := n;
  res := 1;
  while i > 0
    invariant i >= 0
    invariant res * Expt(b, i) == Expt(b, n)
    decreases i
  {
    Expt_unfold(b, i);
    res := res * b;
    i := i - 1;
  }
}
// </vc-code>

