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
    let mut min_length = lists[0].len();
    let mut i = 1;
    
    while i < lists.len()
        invariant
            1 <= i <= lists.len(),
            exists|j: int| #![auto] 0 <= j < i && min_length == lists[j].len(),
            forall|j: int| #![auto] 0 <= j < i ==> min_length <= lists[j].len(),
    {
        if lists[i].len() < min_length {
            min_length = lists[i].len();
        }
        i += 1;
    }
    
    min_length
}

fn main() {}
}