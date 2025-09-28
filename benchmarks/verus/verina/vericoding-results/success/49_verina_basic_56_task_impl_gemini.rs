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
    /* code modified by LLM (iteration 2): fixed invariant syntax and added preconditions */
    let mut result = dest.clone();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            s_start + len <= src.len(),
            d_start + len <= dest.len(),
            result.len() == dest.len(),
            // The part already copied is correct
            forall|k: int| 0 <= k < i ==> 
                #[trigger] result.spec_index(d_start as int + k) == src.spec_index(s_start as int + k),
            // The parts not yet modified (before, and after the copied segment) are equal to the original destination
            forall|j: int| (0 <= j < d_start || d_start + i <= j < dest.len()) ==> 
                #[trigger] result.spec_index(j) == dest.spec_index(j),
        decreases len - i
    {
        let val = src[s_start + i];
        result.set(d_start + i, val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}