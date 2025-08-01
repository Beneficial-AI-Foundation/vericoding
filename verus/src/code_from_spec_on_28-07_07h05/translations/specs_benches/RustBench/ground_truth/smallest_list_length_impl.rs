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
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < lists.len()
        invariant
            0 <= idx <= lists.len(),
            exists|i: int| #![auto] 0 <= i < idx && min_length == lists[i].len(),
            forall|i: int| #![auto] 0 <= i < idx ==> min_length <= lists[i].len(),
        decreases lists.len() - idx
    {
        if lists[idx].len() < min_length {
            min_length = lists[idx].len();
        }
        idx += 1;
    }
    
    min_length
}

fn main() {}
}