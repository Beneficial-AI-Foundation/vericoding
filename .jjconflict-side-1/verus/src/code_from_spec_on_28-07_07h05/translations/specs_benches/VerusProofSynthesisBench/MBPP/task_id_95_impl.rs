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
    let mut j = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while j < list.len()
        invariant
            1 <= j <= list.len(),
            forall|i: int| 0 <= i < j ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < j && min == #[trigger] list[i].len(),
        decreases list.len() - j
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