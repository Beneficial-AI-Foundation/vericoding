// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_score_triangulation(vertices: Vec<u32>) -> (result: u32)
    requires vertices.len() >= 3,
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

}

fn main() {
    // let result1 = min_score_triangulation(vec![1, 2, 3]);
    // assert(result1 == 6);
    
    // let result2 = min_score_triangulation(vec![3, 7, 4, 5]);
    // assert(result2 == 144);
    
    // let result3 = min_score_triangulation(vec![1, 3, 1, 4, 1, 5]);
    // assert(result3 == 13);
}