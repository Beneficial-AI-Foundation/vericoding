// <vc-preamble>
function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for an iterative implementation. */
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Switched to an iterative implementation to satisfy the postcondition. */
{
  p := 1;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant p == Power(i)
  {
    p := 2 * p;
    i := i + 1;
  }
}
// </vc-code>
