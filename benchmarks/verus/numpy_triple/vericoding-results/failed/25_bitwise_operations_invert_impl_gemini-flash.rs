// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed - not needed */
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed potential overflow for negative values in x[i] + 1 and added proof block for postcondition */
{
    let mut result = Vec::new();
    let mut i = 0;
    let old_x_len = x.len();
    while i < x.len()
        invariant
            0 <= i,
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] as int + 1) as i32,
            x.len() == old_x_len,
        decreases x.len() - i
    {
        proof {
            if x[i] != -1 {
                if x[i] > 0 {
                    assert(x[i] as int + 1 > 0);
                    assert(-(x[i] as int + 1) < 0);
                } else if x[i] < 0 {
                    assert(x[i] as int + 1 <= 0);
                    assert(-(x[i] as int + 1) >= 0);
                }
            }
        }
        result.push(-(x[i] as int + 1) as i32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}