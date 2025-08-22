use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

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
    let mut j = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while j < list.len()
        invariant
            1 <= j <= list.len(),
            min >= 0,
            forall|i: int| 0 <= i < j ==> min <= #[trigger] list[i].len(),
            exists|i: int| 0 <= i < j && min == #[trigger] list[i].len(),
        decreases list.len() - j,
    {
        if list[j].len() < min {
            min = list[j].len();
        }
        j += 1;
    }
    
    min
}

} // verus!