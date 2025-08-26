// <vc-spec>
function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
// </vc-helpers>

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

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)