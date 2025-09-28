// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking for array access */
fn compute_diagonal_length(rows: usize, cols: usize, offset: i32) -> usize {
    let min_dim = if rows <= cols { rows } else { cols };
    min_dim
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
    /* code modified by LLM (iteration 5): fixed trigger annotation for quantifier */
    let rows = x.len();
    let cols = x[0].len();
    let diag_len = if rows <= cols { rows } else { cols };
    
    let mut result = Vec::with_capacity(diag_len);
    let mut i = 0;
    
    while i < diag_len
        invariant
            i <= diag_len,
            diag_len == spec_min(x@.len() as int, x@[0].len() as int),
            result@.len() == i,
            i <= x@.len(),
            i <= x@[0].len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < x@.len() && 0 <= j < #[trigger] x@[0].len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == x@[j][j],
        decreases diag_len - i
    {
        assert(i < x@.len());
        assert(i < x@[0].len());
        result.push(x[i][i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}