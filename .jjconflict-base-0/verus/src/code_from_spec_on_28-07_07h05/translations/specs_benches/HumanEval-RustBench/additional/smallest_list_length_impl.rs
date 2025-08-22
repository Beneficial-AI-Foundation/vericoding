use vstd::prelude::*;

verus! {

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
{
    let mut min_length = lists[0].len();
    let mut j = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while j < lists.len()
        invariant
            0 < j <= lists.len(),
            exists|i: int| #![auto] 0 <= i < j && min_length == lists[i].len(),
            forall|i: int| #![auto] 0 <= i < j ==> min_length <= lists[i].len(),
        decreases lists.len() - j
    {
        if lists[j].len() < min_length {
            min_length = lists[j].len();
        }
        j += 1;
    }
    
    min_length
}

fn main() {}
}