// <vc-preamble>
function calculateDeposit(initial: int, years: int): int
    requires initial >= 0
    requires years >= 0
{
    if years == 0 then initial
    else 
        var prevDeposit := calculateDeposit(initial, years - 1);
        prevDeposit + prevDeposit / 100
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The previous implementation of IsSquare was not compilable. This helper is not actually needed by the solve implementation nor useful for the problem. Therefore, remove the entire helper. */

// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (years: int)
    requires X >= 101
    ensures years >= 0
    ensures var finalDeposit := calculateDeposit(100, years); finalDeposit >= X
    ensures years == 0 || calculateDeposit(100, years - 1) < X
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix compilation error in the original code. This helper is not needed for the main method's logic. */
{
  years := 0;
  while calculateDeposit(100, years) < X
    invariant years >= 0
    invariant forall y :: 0 <= y < years ==> calculateDeposit(100, y) < X
  {
    years := years + 1;
  }
}
// </vc-code>
