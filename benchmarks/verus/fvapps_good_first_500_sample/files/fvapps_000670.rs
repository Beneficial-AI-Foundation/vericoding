// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_zebras_spat_at_each_other(positions: Vec<(i32, i32)>) -> (result: bool)
    requires positions.len() > 0,
    ensures 
        result == exists|i: int, j: int| 
            0 <= i < positions.len() && 
            0 <= j < positions.len() && 
            i != j && 
            positions[i].0 + positions[i].1 == positions[j].0 &&
            positions[j].0 + positions[j].1 == positions[i].0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // #eval can_zebras_spit_at_each_other [[0, 1], [1, -1]]
    // #eval can_zebras_spit_at_each_other [[0, 1], [2, -1]]
    // #eval can_zebras_spit_at_each_other [[0, 2], [1, 1], [2, -2]]
}