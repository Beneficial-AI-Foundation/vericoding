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
    let mut last_idx = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= last_idx < a.len(),
            a[last_idx] == elem,
            forall|j: int| last_idx < j < i ==> a[j] != elem,
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