use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    /* code modified by LLM (iteration 2): added requires clause to ensure lists is non-empty */
    requires
        lists.len() > 0,
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
{
    let mut min_length = lists[0].len();
    let mut index = 1;
    
    while index < lists.len()
        invariant
            /* code modified by LLM (iteration 2): simplified invariant since non-empty is now guaranteed by precondition */
            lists.len() > 0,
            1 <= index <= lists.len(),
            exists|j: int| #![auto] 0 <= j < index && min_length == lists[j].len(),
            forall|j: int| #![auto] 0 <= j < index ==> min_length <= lists[j].len(),
        /* code modified by LLM (iteration 2): added decreases clause to ensure loop termination */
        decreases lists.len() - index
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