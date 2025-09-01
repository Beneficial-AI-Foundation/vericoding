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
    let mut min_length = lists[0].len();
    let mut index = 1;
    
    while index < lists.len()
        invariant
            1 <= index <= lists.len(),
            exists|j: int| #![auto] 0 <= j < index ==> min_length == lists[j].len(),
            forall|i: int| #![auto] 0 <= i < index ==> min_length <= lists[i].len(),
        decreases lists.len() - index,
    {
        if lists[index].len() < min_length {
            min_length = lists[index].len();
        }
        index += 1;
    }
    
    min_length
}
// </vc-code>

fn main() {}
}