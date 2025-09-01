use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    // pre-conditions-start
    requires
        lists.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut min_len = lists[0].len();
    let mut i: usize = 1;
    while i < lists.len()
        invariant
            0 <= i,
            i < lists.len() + 1,
            exists|j: int| #![auto] 0 <= j < i && min_len == lists[j as usize].len(),
            forall|k: int| #![auto] 0 <= k < i ==> min_len <= lists[k as usize].len(),
    {
        if lists[i].len() < min_len {
            min_len = lists[i].len();
        }
        i += 1;
    }
    min_len
    // impl-end
}
// </vc-code>

fn main() {}
}