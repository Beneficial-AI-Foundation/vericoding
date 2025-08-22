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
    let mut min_len = lists[0].len();
    let mut idx = 0;
    
    while idx < lists.len()
        invariant
            0 <= idx <= lists.len(),
            exists|i: int| #![auto] 0 <= i < idx ==> min_len == lists[i].len(),
            forall|i: int| #![auto] 0 <= i < idx ==> min_len <= lists[i].len(),
            min_len == lists[0].len() || exists|i: int| #![auto] 0 <= i < idx && min_len == lists[i].len(),
    {
        if lists[idx].len() < min_len {
            min_len = lists[idx].len();
        }
        idx += 1;
    }
    
    min_len
}

fn main() {}
}