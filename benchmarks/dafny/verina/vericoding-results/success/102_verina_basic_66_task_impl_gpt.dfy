// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replace 'function method' with 'function' to satisfy --function-syntax:4 */
function IsEven(x: int): bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method ComputeIsEven(x: int) returns (result: bool)
    ensures result == true <==> x % 2 == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result directly to meet postcondition */
  result := x % 2 == 0;
}
// </vc-code>
