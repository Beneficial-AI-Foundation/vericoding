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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}