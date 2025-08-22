use vstd::prelude::*;

verus! {

//IMPL last_position
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
    /* code modified by LLM (iteration 1): initialize pos to find first occurrence, then continue to find last */
    let mut pos = 0;
    let mut i = 0;
    
    // First find any occurrence to initialize pos properly
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != elem,
        decreases a.len() - i
    {
        if a[i] == elem {
            pos = i;
            break;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): continue from current position to find the last occurrence */
    i += 1; // Move to next position after the found element
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= pos < a.len(),
            a[pos as int] == elem,
            forall|j: int| pos < j < i ==> a[j] != elem,
        decreases a.len() - i
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