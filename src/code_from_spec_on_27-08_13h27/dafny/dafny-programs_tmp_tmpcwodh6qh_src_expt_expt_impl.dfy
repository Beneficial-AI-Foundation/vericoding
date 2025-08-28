ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma ExptLemma(b: int, n: nat)
  ensures Expt(b, n) == if n == 0 then 1 else b * Expt(b, n - 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ExptImpl(b: int, n: nat) returns (res: int)
  ensures res == Expt(b, n)
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
