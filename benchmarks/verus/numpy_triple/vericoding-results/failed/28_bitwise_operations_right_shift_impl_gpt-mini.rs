// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate non-negative */
spec fn is_nonneg(x: i32) -> bool { x >= 0 }
/* helper modified by LLM (iteration 5): predicate non-positive */
spec fn is_nonpos(x: i32) -> bool { x <= 0 }
/* helper modified by LLM (iteration 5): division-shift equivalence for non-negative */
spec fn shift_div_equiv(x: i32, s: i32) -> bool { (x >= 0 && s >= 0) ==> (x >> s == x / (1i32 << s)) }
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
{
    /* code modified by LLM (iteration 5): compute per-element using division for non-negative x and arithmetic shift for negative x */
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < x1.len()
        invariant 0 <= i && i <= x1.len()
        invariant result.len() == i
        invariant forall|j: int| 0 <= j && j < i ==> {
            &&& (x1@[j] >= 0 ==> result@[j] == x1@[j] / (1i32 << x2@[j]))
            &&& (x1@[j] < 0 ==> result@[j] == x1@[j] >> x2@[j])
            &&& (x2@[j] == 0 ==> result@[j] == x1@[j])
            &&& (x1@[j] > 0 ==> result@[j] >= 0)
            &&& (x1@[j] < 0 ==> result@[j] <= 0)
            &&& (x1@[j] == 0 ==> result@[j] == 0)
        }
        decreases x1.len() - i
    {
        let xi: i32 = x1@[i];
        let si: i32 = x2@[i];
        assert(si >= 0);
        if xi >= 0 {
            let r: i32 = xi / (1i32 << si);
            result.push(r);
            proof {
                assert(xi >= 0);
                assert(result@[i] == xi / (1i32 << si));
            }
        } else {
            let r: i32 = xi >> si;
            result.push(r);
            proof {
                assert(xi < 0);
                assert(result@[i] == xi >> si);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}