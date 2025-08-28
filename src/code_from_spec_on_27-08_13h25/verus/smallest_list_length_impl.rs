use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut smallest_len = lists[0].len();
    let mut i: usize = 1;

    while i < lists.len()
        invariant
            0 < i <= lists.len(),
            exists|k: int| #![auto] 0 <= k < i as int && smallest_len == lists[k].len(),
            forall|k: int| #![auto] 0 <= k < i as int ==> smallest_len <= lists[k].len(),
        decreases lists.len() - i
    {
        if lists[i].len() < smallest_len {
            smallest_len = lists[i].len();
        }
        i = i + 1;
    }

    smallest_len
}
// </vc-code>

fn main() {}
}