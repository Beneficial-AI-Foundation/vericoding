use vstd::prelude::*;

verus! {

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
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
    let mut min = list[0].len();
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < list.len()
        invariant
            0 <= idx <= list.len(),
            forall|i: int| 0 <= i < idx ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < idx && min == #[trigger] list[i].len(),
        decreases list.len() - idx
    {
        if list[idx].len() < min {
            min = list[idx].len();
        }
        idx += 1;
    }
    
    min
}

} // verus!

fn main() {}