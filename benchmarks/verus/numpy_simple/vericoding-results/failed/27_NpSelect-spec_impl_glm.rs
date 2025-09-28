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
    /* code modified by LLM (iteration 2): added loop invariants for bounds and fixed algorithm to take first true condition */
    let n = condlist[0].len();
    let mut result = Vec::with_capacity(n);
    for j in 0..n
        invariant
            result@.len() == j,
            forall|i: int, j2: int| 
                0 <= i < condlist@.len() && 0 <= j2 < j && condlist@[i][j2] ==> 
                result@[j2] == choicelist@[i][j2],
    {
        let mut value = 0.0;
        let mut found = false;
        for i in 0..condlist.len()
            invariant
                0 <= j < n,
                0 <= i <= condlist@.len(),
                i < condlist@.len() ==> j < condlist@[i].len(),
                i < condlist@.len() ==> j < choicelist@[i].len(),
                found ==> (exists|k: int| 0 <= k < i && condlist@[k][j]),
        {
            if condlist[i][j] {
                if !found {
                    value = choicelist[i][j];
                    found = true;
                }
            }
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