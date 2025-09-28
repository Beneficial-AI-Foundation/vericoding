// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing unsupported core::cmp::min with inline min logic and ensured diag_len is the minimum of rows and cols */
    let mut result = Vec::new();
    let rows = x.len() as usize;
    let cols = if x.len() > 0 {
        x[0].len()
    } else {
        0
    };
    let mut i = 0;
    let diag_len = if rows < cols { rows } else { cols };
    while i < diag_len
        invariant
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k] == x@[k][k]
        decreases diag_len - i
    {
        let elem = x[i][i];
        result.push(elem);
        i += 1;
    }
    proof {
        assert(result@.len() == spec_min(x@.len() as int, x@[0].len() as int));
        assert(offset == 0 ==> forall|i: int| 0 <= i < result@.len() ==> 
            result@[i] == x@[i][i]);
        assert(forall|i: int| 0 <= i < result@.len() ==> 
            exists|r: int, c: int| 
                0 <= r < x@.len() && 0 <= c < x@[0].len() &&
                #[trigger] result@[i] == x@[r][c]);
    }
    result
}
// </vc-code>

}
fn main() {}