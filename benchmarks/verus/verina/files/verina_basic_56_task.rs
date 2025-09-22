// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn copy(src: &Vec<i8>, s_start: usize, dest: &Vec<i8>, d_start: usize, len: usize) -> (result: Vec<i8>)
    requires 
        src.len() >= s_start + len,
        dest.len() >= d_start + len,
    ensures
        result.len() == dest.len(),
        forall|i: int| 0 <= i < d_start as int ==> #[trigger] result@[i] == dest@[i],
        forall|i: int| d_start as int + len as int <= i < result.len() as int ==> #[trigger] result@[i] == dest@[i],
        forall|i: int| 0 <= i < len as int ==> #[trigger] result@[d_start as int + i] == #[trigger] src@[s_start as int + i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}