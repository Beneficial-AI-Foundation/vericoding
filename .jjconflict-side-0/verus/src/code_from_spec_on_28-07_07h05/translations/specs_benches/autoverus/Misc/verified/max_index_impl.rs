use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    requires
        x.len() >= 1,
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
{
    let mut max_idx = 0;
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < x.len()
        invariant
            max_idx < x.len(),
            i <= x.len(),
            forall|k: int| 0 <= k < i ==> x[max_idx as int] >= x[k],
        decreases x.len() - i
    {
        if x[i] > x[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}

} // verus!