// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial helper retained */
spec fn dummy() -> bool { true }
// </vc-helpers>

// <vc-spec>
fn myfun1(x: &Vec<i32>) -> (max_index: usize)

    requires
        x.len() >= 1,

    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize indexing and maintain invariant over processed prefix */
    let mut i: usize = 1;
    let mut max_index: usize = 0;
    while i < x.len()
        invariant
            max_index < x.len(),
            forall|k: int| 0 <= k < i as int ==> x[max_index as int] >= x[k],
        decreases x.len() - i
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        i = i + 1;
    }
    max_index
}
// </vc-code>

}
fn main() {}