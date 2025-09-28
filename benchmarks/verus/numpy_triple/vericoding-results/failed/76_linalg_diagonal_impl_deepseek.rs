// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma_usize_max and lemma_min_properties */
proof fn lemma_usize_max()
    ensures
        usize::MAX as int == usize::MAX,
{
}

proof fn lemma_min_properties(a: int, b: int)
    ensures
        spec_min(a, b) <= a,
        spec_min(a, b) <= b,
{
}

proof fn lemma_index_bounds(x: Vec<Vec<f32>>, i: int)
    requires
        0 <= i < x@.len(),
        forall|j: int| 0 <= j < x@.len() ==> #[trigger] x@[j].len() > 0,
        forall|j: int| 0 <= j < x@.len() ==> #[trigger] x@[j].len() == x@[0].len()
    ensures
        0 <= i < x@.len(),
        forall|k: int| 0 <= k < x@[i].len() ==> 0 <= k < x@[0].len()
{
    proof {
        assert forall|k: int| 0 <= k < x@[i].len() implies 0 <= k < x@[0].len() by {
            assert(x@[i].len() == x@[0].len());
        };
    }
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
    /* code modified by LLM (iteration 5): removed calls to undefined lemmas and simplified bounds checking */
    let n = x.len();
    let m = x[0].len();
    let diag_len = if n <= m { n } else { m };
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < diag_len
        invariant
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == x@[i][i],
            0 <= idx <= diag_len,
            diag_len == spec_min(n as int, m as int) as usize
        decreases diag_len - idx
    {
        assert(0 <= idx < n) by {
            assert(spec_min(n as int, m as int) <= n as int);
        };
        assert(0 <= idx < m) by {
            assert(spec_min(n as int, m as int) <= m as int);
        };
        proof {
            lemma_index_bounds(x, idx as int);
        }
        let row = &x[idx];
        let elem = row[idx];
        result.push(elem);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}