use vstd::prelude::*;

verus! {

//IMPL smallest_list_length
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        list.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed function structure and implemented function body to find minimum list length */
    let mut min = list[0].len();
    let mut j = 1;
    
    while j < list.len()
        invariant
            1 <= j <= list.len(),
            forall|i: int| 0 <= i < j ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < j && min == #[trigger] list[i].len(),
    {
        if list[j].len() < min {
            min = list[j].len();
        }
        j += 1;
    }
    
    min
}

} // verus!

fn main() {}