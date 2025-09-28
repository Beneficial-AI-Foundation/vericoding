// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn copy(src: &Vec<i32>, s_start: usize, dest: &Vec<i32>, d_start: usize, len: usize) -> (result: Vec<i32>)
    requires 
        src.len() >= s_start + len,
        dest.len() >= d_start + len,
    ensures
        result.len() == dest.len(),
        forall|i: int| 0 <= i < d_start ==> #[trigger] result[i] == dest[i],
        forall|i: int| d_start + len <= i < result.len() ==> #[trigger] result[i] == dest[i],
        forall|i: int| 0 <= i < len ==> #[trigger] result[d_start + i] == #[trigger] src[s_start + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Strengthened loop invariants for strict bounds checking */
    let mut result = dest.clone();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == dest.len(),
            s_start + len <= src.len(),
            d_start + len <= dest.len(),
            i < len ==> s_start + i < src.len(),
            i < len ==> d_start + i < dest.len(),
            forall|j: int| 0 <= j < d_start ==> #[trigger] result[j] == dest[j],
            forall|j: int| d_start + len <= j < result.len() ==> #[trigger] result[j] == dest[j],
            forall|j: int| 0 <= j < i ==> #[trigger] result[d_start + j] == #[trigger] src[s_start + j],
            forall|j: int| i <= j < len && d_start + j < result.len() ==> #[trigger] result[d_start + j] == #[trigger] dest[d_start + j],
        decreases len - i
    {
        result.set(d_start + i, src[s_start + i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}