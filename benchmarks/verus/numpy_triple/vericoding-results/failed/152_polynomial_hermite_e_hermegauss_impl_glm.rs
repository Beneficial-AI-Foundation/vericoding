// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed to spec function for ghost code compatibility */
spec fn compute_point_value(index: int) -> i8 {
    #[verifier::truncate] (index - 128) as i8
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
    /* code modified by LLM (iteration 5): Replaced int cast with usize arithmetic and added proof */
    let mut points: Vec<i8> = Vec::new();
    let mut weights: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < deg
        invariant
            0 <= i <= deg,
            points.len() == i,
            weights.len() == i,
            forall|k: int, l: int| 0 <= k < l < i ==> points@[k] < points@[l],
            forall|k: int| 0 <= k < i ==> weights@[k] == 1,
            forall|k: int| 0 <= k < i ==> points@[k] == compute_point_value(k),
        decreases deg - i,
    {
        let point_value = (i.wrapping_sub(128)) as i8;
        points.push(point_value);
        weights.push(1);
        proof {
            let ghost_index = i as int;
            assert(points@[i] == compute_point_value(ghost_index));
        }
        i += 1;
    }
    (points, weights)
}
// </vc-code>


}
fn main() {}