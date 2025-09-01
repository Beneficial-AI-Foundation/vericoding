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
    // impl-start
    let mut smallest_len: usize = lists[0].len();
    let mut i: usize = 1;

    while i < lists.len()
        invariant
            0 < i,
            i <= lists.len(),
            smallest_len == (Seq::new(lists.len(), |j: int| lists[j as usize].len() as nat).subsequence(0, i as int).min().unwrap_or(lists[0].len() as nat)) as usize,
    {
        if lists[i].len() < smallest_len {
            smallest_len = lists[i].len();
        }
        i = i + 1;
    }
    smallest_len
    // impl-end
}
// </vc-code>

fn main() {}
}