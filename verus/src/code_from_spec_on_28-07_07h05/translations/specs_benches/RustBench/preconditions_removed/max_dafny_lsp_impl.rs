use vstd::prelude::*;

verus! {

//IMPL max
#[verifier::loop_isolation(false)]
fn max(a: &[i32]) -> (x: usize)
    requires
        a.len() > 0,
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
{
    let mut max_idx = 0;
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): updated invariants to be satisfied initially and added decreases clause */
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
        decreases a.len() - i,
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}

fn main() {}
}