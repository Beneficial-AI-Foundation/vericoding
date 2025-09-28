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
    /* code modified by LLM (iteration 2): added decreases clause and basic invariant to while loop */
    let len_cond = condlist.len();
    let len_j = condlist[0].len();
    let mut result = Vec::with_capacity(len_j);
    for j in 0..len_j {
        let mut i = 0;
        let mut value = 0.0;
        let mut found = false;
        while i < len_cond
            invariant
                i <= len_cond,
                found == false,
            decreases len_cond - i
        {
            if condlist[i][j] {
                value = choicelist[i][j];
                found = true;
                break;
            }
            i = i + 1;
        }
        if found {
            result.push(value);
        } else {
            result.push(0.0);
        }
    }
    result
}
// </vc-code>


}
fn main() {}