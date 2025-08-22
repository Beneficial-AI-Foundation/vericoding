use vstd::prelude::*;

verus! {

fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    // pre-conditions-start
    requires
        x.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
    // post-conditions-end
{
    let mut max_index: usize = 0;
    let mut i: usize = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < x.len()
        invariant
            max_index < x.len(),
            i <= x.len(),
            forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
        decreases x.len() - i
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        i = i + 1;
    }
    
    max_index
}

} // verus!

fn main() {}