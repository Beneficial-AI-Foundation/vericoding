use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    requires
        lists.len() > 0,
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
