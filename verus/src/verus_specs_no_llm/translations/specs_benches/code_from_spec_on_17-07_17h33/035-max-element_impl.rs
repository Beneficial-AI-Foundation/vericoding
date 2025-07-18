use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 1): Fixed function signature syntax and moved requires/ensures clauses to correct position */
fn max_element(a: &Vec<i32>) -> (max: i32)
    requires
        a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
{
    /* code modified by LLM (iteration 1): Removed incorrect return statement and implemented proper function body */
    let mut max = a[0];
    let mut idx = 1;
    
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a[i] <= max,
            exists|i: int| 0 <= i < idx && a[i] == max,
        decreases a.len() - idx,
    {
        if a[idx] > max {
            max = a[idx];
        }
        idx += 1;
    }
    
    max
}

}
fn main() {}