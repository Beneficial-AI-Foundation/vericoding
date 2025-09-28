// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
    ensures
        result@.len() == mat@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == mat@[i].len(),

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i == j 
            ==> #[trigger] result@[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i != j 
            ==> #[trigger] result@[i][j] == mat@[i][j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [split loop invariant to guide verifier] */
{
    let mut result = mat;
    let mut i: usize = 0;
    while i < result.len()
        invariant
            i <= result.len(),
            result@.len() == mat@.len(),
            forall|k: int| 0 <= k < result@.len() ==> result@[k].len() == mat@[k].len(),
            forall|k: int, j: int|
                0 <= k < i as int && 0 <= j < result@[k].len() ==>
                if k == j { result@[k][j] == val } else { result@[k][j] == mat@[k][j] },
            forall|k: int, j: int|
                i as int <= k < result@.len() && 0 <= j < result@[k].len() ==>
                result@[k][j] == mat@[k][j],
        decreases result.len() - i
    {
        if i < result[i].len() {
            let mut new_row = result[i].clone();
            new_row.set(i, val);
            result.set(i, new_row);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}