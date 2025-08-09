use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
{
    let mut pos = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= pos < a.len(),
            a[pos as int] == elem,
            forall|j: int| pos < j < i ==> a[j] != elem,
    {
        if a[i] == elem {
            pos = i;
        }
        i += 1;
    }
    
    pos
}

fn main() {}
}