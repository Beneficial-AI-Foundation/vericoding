// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min_helper(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed method implementation */
  m := min_helper(a, b);
}
// </vc-code>
