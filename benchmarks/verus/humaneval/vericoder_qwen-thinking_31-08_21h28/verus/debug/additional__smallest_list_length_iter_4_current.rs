use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut min_len = lists[0].len();
    let mut i: int = 1;
    while i < lists.len() as int {
        loop invariant { (forall j: int :: #![trigger] 0 <= j < i ==> min_len <= lists[j].len()) }
        if lists[i as usize].len() < min_len {
            min_len = lists[i as usize].len();
        }
        i = i + 1;
    }
    min_len
}
// </vc-code>

fn main() {}
}