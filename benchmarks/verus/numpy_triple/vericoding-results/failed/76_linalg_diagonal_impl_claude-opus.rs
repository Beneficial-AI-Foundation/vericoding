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
    /* code modified by LLM (iteration 4): Fixed type mismatch by converting usize to int for comparison */
    let n = x.len();
    let m = x[0].len();
    let min_dim = if n <= m { n } else { m };
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < min_dim
        invariant
            i <= min_dim,
            min_dim == spec_min(n as int, m as int),
            result@.len() == i as int,
            n == x@.len(),
            m == x@[0].len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < x@.len() && 0 <= j < x@[0].len(),
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j][j],
            forall|j: int| 0 <= j < result@.len() ==> 
                exists|r: int, c: int| 
                    0 <= r < x@.len() && 0 <= c < x@[0].len() &&
                    #[trigger] result@[j] == x@[r][c],
        decreases min_dim - i
    {
        assert(i < n);
        assert(i < m);
        assert((i as int) < x@.len());
        assert((i as int) < x@[i].len());
        result.push(x[i][i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}