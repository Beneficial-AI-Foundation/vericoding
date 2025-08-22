use vstd::prelude::*;

verus! {

fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
{
    let mut max = a[0];
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a[i] <= max,
            exists|i: int| 0 <= i < idx && a[i] == max,
        decreases a.len() - idx
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