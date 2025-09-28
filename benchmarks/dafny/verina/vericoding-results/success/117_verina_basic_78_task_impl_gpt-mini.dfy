// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute tuple (x+y, x-y) */
function ComputeResult(x: int, y: int): (int, int) {
  (x + y, x - y)
}
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): assign computed tuple to result */
  result := ComputeResult(x, y);
}
// </vc-code>
