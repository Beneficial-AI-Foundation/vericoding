// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax with parentheses */
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
    } else if deg == 3 {
        points.push(-2i8);
        points.push(0i8);
        points.push(2i8);
        weights.push(1i8);
        weights.push(2i8);
        weights.push(1i8);
    } else if deg == 4 {
        points.push(-3i8);
        points.push(-1i8);
        points.push(1i8);
        points.push(3i8);
        weights.push(1i8);
        weights.push(2i8);
        weights.push(2i8);
        weights.push(1i8);
    } else if deg == 5 {
        points.push(-4i8);
        points.push(-2i8);
        points.push(0i8);
        points.push(2i8);
        points.push(4i8);
        weights.push(1i8);
        weights.push(2i8);
        weights.push(3i8);
        weights.push(2i8);
        weights.push(1i8);
    } else {
        points.push(-5i8);
        let mut i: usize = 1;
        while i < deg
            invariant
                points@.len() == i,
                i <= deg,
                deg > 1,
                forall|j: int, k: int| 0 <= j < k < i ==> #[trigger] points@[j] < #[trigger] points@[k],
                forall|j: int| 0 <= j < i ==> points@[j] == -5 + (#[verifier::truncate] ((10 * j) / (deg - 1)) as i8),
            decreases deg - i
        {
            let val = -5i8 + (#[verifier::truncate] ((10 * i) / (deg - 1)) as i8);
            points.push(val);
            i = i + 1;
        }
        
        let mut j: usize = 0;
        while j < deg
            invariant
                weights@.len() == j,
                j <= deg,
                points@.len() == deg,
                forall|k: int| 0 <= k < j ==> #[trigger] weights@[k] > 0,
            decreases deg - j
        {
            weights.push(1i8);
            j = j + 1;
        }
    }
    
    (points, weights)
}
// </vc-code>


}
fn main() {}