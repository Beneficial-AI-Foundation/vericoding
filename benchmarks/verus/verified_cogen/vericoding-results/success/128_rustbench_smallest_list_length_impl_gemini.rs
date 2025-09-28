// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut min_len = lists[0].len();
    let mut i: usize = 1;

    while i < lists.len()
        invariant
            0 < i <= lists.len(),
            exists|k: int| 0 <= k < i && min_len == lists[k].len(),
            forall|k: int| 0 <= k < i ==> min_len <= lists[k].len(),
        decreases lists.len() - i
    {
        if lists[i].len() < min_len {
            min_len = lists[i].len();
        }
        i = i + 1;
    }

    min_len
}
// </vc-code>

}
fn main() {}