// <vc-preamble>
ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}
// </vc-preamble>

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
    invariant 0 <= i <= n
    invariant res == Expt(b, i)
  {
    res := res * b;
    i := i + 1;
  }
}
// </vc-code>
