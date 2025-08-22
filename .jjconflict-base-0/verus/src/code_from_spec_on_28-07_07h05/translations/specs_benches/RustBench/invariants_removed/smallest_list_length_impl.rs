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
    let mut index = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while index < lists.len()
        invariant
            0 < index <= lists.len(),
            min_length == lists[0].len() || exists|j: int| #![auto] 1 <= j < index && min_length == lists[j].len(),
            forall|j: int| #![auto] 0 <= j < index ==> min_length <= lists[j].len(),
        decreases lists.len() - index,
    {
        if lists[index].len() < min_length {
            min_length = lists[index].len();
        }
        index += 1;
    }
    
    min_length
}

fn main() {}
}