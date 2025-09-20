// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        condlist@.len() > 0,
        condlist@.len() == choicelist@.len(),
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len(),
        forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> 
            condlist@[i].len() == condlist@[j].len(),
    ensures
        result@.len() == condlist@[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist@.len() && 0 <= j < result@.len() && condlist@[i][j] ==> 
            result@[j] == choicelist@[i][j],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}