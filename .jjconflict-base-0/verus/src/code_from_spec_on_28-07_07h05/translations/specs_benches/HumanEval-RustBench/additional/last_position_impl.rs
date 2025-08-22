use vstd::prelude::*;

verus! {

//IMPL last_position
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): initialize pos to first occurrence of elem to satisfy loop invariants */
    let mut pos = 0;
    let mut i = 0;
    
    // Find the first occurrence to initialize pos properly
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
    
    // Continue from where we left off to find the last occurrence
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