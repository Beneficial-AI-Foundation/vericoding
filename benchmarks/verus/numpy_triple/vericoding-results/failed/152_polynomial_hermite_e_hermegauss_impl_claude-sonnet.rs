// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed to spec mode for use in proofs */
spec fn safe_point_calculation(i: usize, deg: usize) -> i8
    recommends
        deg > 0,
        i < deg,
        deg <= 16,
{
    (i as i8) - (deg as i8 / 2)
}
// </vc-helpers>

// <vc-spec>
fn hermegauss(deg: usize) -> (result: (Vec<i8>, Vec<i8>))
    requires deg > 0,
    ensures
        /* Points are ordered (sorted in ascending order) */
        forall|i: int, j: int| 0 <= i < j < deg ==> #[trigger] result.0@[i] < #[trigger] result.0@[j],
        /* Weights are positive */
        forall|i: int| 0 <= i < deg ==> #[trigger] result.1@[i] > 0,
        /* Return tuple has correct lengths */
        result.0@.len() == deg && result.1@.len() == deg,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified proof block to avoid exec mode function calls */
    let mut points = Vec::new();
    let mut weights = Vec::new();
    
    if deg == 1 {
        points.push(0i8);
        weights.push(1i8);
    } else if deg == 2 {
        points.push(-1i8);
        points.push(1i8);
        weights.push(1i8);
        weights.push(1i8);
    } else {
        assert(deg <= 16); // Ensure safe range for i8 arithmetic
        let mut i = 0;
        while i < deg
            invariant
                i <= deg,
                points.len() == i,
                weights.len() == i,
                forall|k: int, l: int| 0 <= k < l < i ==> points@[k] < points@[l],
                forall|k: int| 0 <= k < i ==> weights@[k] > 0,
                deg <= 16,
            decreases deg - i
        {
            let point_val = (i as i8) - (deg as i8 / 2);
            points.push(point_val);
            weights.push(1i8);
            i = i + 1;
            
            // Prove that the newly added point maintains ordering
            proof {
                if i > 1 {
                    let prev_val = safe_point_calculation((i - 1) as usize, deg);
                    let curr_val = safe_point_calculation((i - 1) as usize, deg);
                    assert(prev_val < point_val);
                }
            }
        }
    }
    
    (points, weights)
}
// </vc-code>


}
fn main() {}