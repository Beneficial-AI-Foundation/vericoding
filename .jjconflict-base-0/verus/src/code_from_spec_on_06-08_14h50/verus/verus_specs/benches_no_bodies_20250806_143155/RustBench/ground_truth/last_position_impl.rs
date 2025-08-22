use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
{
    /* code modified by LLM (iteration 1): Added decreases clause to first while loop */
    let mut last_idx: usize = 0;
    let mut i: usize = 0;
    
    // Find any initial occurrence to establish the invariant
    while i < a.len() && a[i] != elem
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != elem,
        decreases a.len() - i,
    {
        i += 1;
    }
    
    last_idx = i;
    i += 1;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= last_idx < a.len(),
            a[last_idx as int] == elem,
            forall|j: int| last_idx < j < i ==> a[j] != elem,
        decreases a.len() - i,
    {
        if a[i] == elem {
            last_idx = i;
        }
        i += 1;
    }
    
    last_idx
}

fn main() {}
}