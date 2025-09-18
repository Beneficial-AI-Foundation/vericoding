// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors related to `nat` and `int` in non-ghost contexts by using `usize` for all indices and intermediate calculations. */
{
    let n = a.len();
    let mut result = Vec::new();
    result.reserve(n);

    if n == 0 {
        return result;
    }

    let normalized_offset: usize = (offset % (n as int)) as usize;

    for i in 0..n {
        let src_idx_val: usize = (i + normalized_offset) % n;
        result.push(a[src_idx_val]);
    }
    result
}
// </vc-code>

}
fn main() {}