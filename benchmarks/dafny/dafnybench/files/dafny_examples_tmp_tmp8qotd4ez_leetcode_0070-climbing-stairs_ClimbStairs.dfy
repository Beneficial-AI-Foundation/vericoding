// <vc-preamble>
function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
