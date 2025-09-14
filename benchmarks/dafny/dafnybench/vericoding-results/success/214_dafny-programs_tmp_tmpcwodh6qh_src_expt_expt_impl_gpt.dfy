ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// <vc-code>
{
  res := 1;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant res == Expt(b, i)
    decreases n - i
  {
    assert i + 1 != 0;
    assert Expt(b, i + 1) == b * Expt(b, i);
    res := b * res;
    i := i + 1;
  }
}
// </vc-code>

