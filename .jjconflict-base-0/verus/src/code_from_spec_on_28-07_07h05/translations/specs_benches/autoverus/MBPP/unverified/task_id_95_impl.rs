use vstd::prelude::*;

fn main() {}

verus! {

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < list.len()
        invariant
            1 <= idx <= list.len(),
            min >= 0,
            forall|i: int| 0 <= i < idx ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < idx && min == #[trigger] list[i].len(),
        decreases list.len() - idx,
    {
        if list[idx].len() < min {
            min = list[idx].len();
        }
        idx += 1;
    }
    
    min
}

} // verus!