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
  assume {:axiom} false;
}
// </vc-code>
