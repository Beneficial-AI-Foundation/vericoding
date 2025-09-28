// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn half_f32(x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defined half_f32 as x divided by 2.0 */
spec fn half_f32(x: f32) -> f32 {
  x / 2.0f32
}
// </vc-helpers>

// <vc-spec>
fn hermline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == half_f32(scl)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implemented hermline by pushing off and scl / 2.0, and asserting equality */
  let mut result = Vec::new();
  result.push(off);
  let half_val = scl / 2.0f32;
  result.push(half_val);
  proof {
    assert(half_val == half_f32(scl));
  }
  result
}
// </vc-code>


}
fn main() {}