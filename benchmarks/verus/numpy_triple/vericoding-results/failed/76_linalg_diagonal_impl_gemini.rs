// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes] */
fn min(a: usize, b: usize) -> (result: usize)
    ensures
        result as int == spec_min(a as int, b as int),
        result <= a,
        result <= b,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

fn numpy_diagonal(x: Vec<Vec<f32>>, offset: i32) -> (result: Vec<f32>)
    requires 
        x@.len() > 0,
        x@.len() < usize::MAX,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result@.len() == spec_min(x@.len() as int, x@[0].len() as int),
        offset == 0 ==> forall|i: int| 0 <= i < result@.len() ==> 
            result@[i] == x@[i][i],
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|r: int, c: int| 
                0 <= r < x@.len() && 0 <= c < x@[0].len() &&
                #[trigger] result@[i] == x@[r][c],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Fix compilation error by casting to int in invariant] */
    let rows = x.len();
    let cols = x[0].len();
    
    let diag_len = min(rows, cols);

    let mut result: Vec<f32> = Vec::with_capacity(diag_len);
    
    let mut i: usize = 0;
    while i < diag_len
        invariant
            i <= diag_len,
            diag_len as int == spec_min(x@.len() as int, x@[0].len() as int),
            result@.len() == i as int,
            forall|k: int| 0 <= k < x@.len() ==> #[trigger] x@[k].len() == x@[0].len(),
            offset == 0 ==> forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == x@[j][j],
            forall|j: int| 0 <= j < i ==> 
                exists|r: int, c: int| 
                    0 <= r < x@.len() && 0 <= c < x@[0].len() &&
                    #[trigger] result@[j] == x@[r][c],
        decreases diag_len - i
    {
        let val = x[i][i];
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}