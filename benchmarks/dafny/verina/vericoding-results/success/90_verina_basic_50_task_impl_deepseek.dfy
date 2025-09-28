// <vc-preamble>
function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 2): removed duplicate abs function */

// </vc-helpers>

// <vc-spec>
method abs_impl(x: int) returns (result: int)
    ensures (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no changes needed to implementation */
  if x >= 0 {
    result := x;
  } else {
    result := -x;
  }
}
// </vc-code>
