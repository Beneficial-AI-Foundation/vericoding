// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed variable name typo `current_current_max_index` to `current_max_index` */
fn max_index_in_vec(x: &Vec<i32>) -> (max_index: usize)
    requires
        x.len() >= 1,
    ensures
        max_index < x.len(),
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
{
    let mut current_max_index: usize = 0;
    let mut i: usize = 1;
    while i < x.len()
        invariant
            0 < i <= x.len(),
            current_max_index < x.len(),
            forall|k: int| 0 <= k < i ==> x[current_max_index as int] >= x[k],
        decreases x.len() - i,
    {
        if x[i] > x[current_max_index] {
            current_max_index = i;
        }
        i = i + 1;
    }
    current_max_index
}
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
/* code modified by LLM (iteration 3): No changes needed in this section as helper was fixed. */
{
    max_index_in_vec(x)
}
// </vc-code>

}
fn main() {}