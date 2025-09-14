// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min for usize */
fn min_usize(a: usize, b: usize) -> usize { if a <= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    requires
        lists.len() > 0,
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate to find minimal list length using spec-level indexing */
    let mut i: usize = 1;
    let mut result: usize = lists[0].len();
    let total: usize = lists.len();
    while i < total
        invariant
            0 <= i as int,
            i as int <= total as int,
            forall|j: int| 0 <= j && j < i as int ==> result <= lists[j].len(),
            exists|k: int| 0 <= k && k < i as int && result == lists[k].len(),
        decreases total - i
    {
        let cur: usize = lists[i].len();
        if cur < result {
            result = cur;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}