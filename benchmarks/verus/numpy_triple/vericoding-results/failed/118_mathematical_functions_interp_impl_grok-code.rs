// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations to quantifiers in invariant to fix verification trigger error */
    let mut result = Vec::with_capacity(x.len());
    let max_i: usize = xp.len() - 1;
    for k in 0..x.len()
        invariant
            k as int <= x.len(),
            result.len() == k as usize,
        decreases x.len() - k
    {
        let x_val = x[k];
        proof {
            assert(xp.len() > 0);
            assert(fp.len() == xp.len());
        }
        if x_val <= xp[0] {
            result.push(fp[0]);
        } else {
            let mut i: usize = 0;
            while i < max_i && x_val >= xp[i + 1]
                invariant
                    i <= max_i,
                    forall|j: int| 0 <= j < i as int ==> #[trigger] (xp@[j + 1]) x_val >= xp@[j + 1],
                    forall|j: int| 0 <= j == i as int ==> #[trigger] (xp@[j]) x_val >= xp@[j] || i == 0,
                decreases max_i + 1 - i
            {
                i = i + 1;
            }
            result.push(if i < max_i { fp[i] } else { fp[max_i] });
        }
    }
    result
}
// </vc-code>

}
fn main() {}