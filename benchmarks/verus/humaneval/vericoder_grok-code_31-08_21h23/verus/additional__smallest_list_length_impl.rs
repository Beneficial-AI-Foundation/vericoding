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
    let mut result: usize = lists[0].len();
    let mut i: usize = 1;
    while i < lists.len()
        invariant 
            1 <= i <= lists.len(),
            exists|j: int| #![auto] 0 <= j < i && result == lists[j].len(),
            forall|j: int| #![auto] 0 <= j < i ==> result <= lists[j].len(),
        decreases
            lists.len() - i,
    {
        if lists[i].len() < result {
            result = lists[i].len();
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}