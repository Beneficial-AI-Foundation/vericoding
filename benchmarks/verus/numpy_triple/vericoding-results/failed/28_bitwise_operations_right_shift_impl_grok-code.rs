// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed ensures to use commas for multiple ensures and removed verification bypass */
fn right_shift_elem(x: i32, s: i32) -> (r: i32)
    requires
        s >= 0,
    ensures
        (x >= 0 ==> r == x / (1i32 << s)),
        (x < 0 ==> r == x >> s),
        (s == 0 ==> r == x),
        (x > 0 ==> r >= 0),
        (x < 0 ==> r <= 0),
        (x == 0 ==> r == 0)
{
    if x >= 0 {
        x / (1i32 << s)
    } else {
        x >> s
    }
}
// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented vector mapping with right shift helper */
{
    let mut result = Vec::with_capacity(x1.len());
    for i in 0..x1.len()
    {
        result.push(right_shift_elem(x1[i], x2[i]));
    }
    result
}
// </vc-code>

}
fn main() {}