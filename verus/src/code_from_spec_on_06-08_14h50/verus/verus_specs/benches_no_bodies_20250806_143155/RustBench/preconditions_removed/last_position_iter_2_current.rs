use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        a.len() > 0,
        exists|k: int| 0 <= k < a.len() && a[k] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
{
    let mut i = a.len() - 1;
    
    loop
        invariant
            0 <= i < a.len(),
            forall|j: int| i < j < a.len() ==> a[j] != elem,
        decreases i
    {
        if a[i] == elem {
            return i;
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    
    /* code modified by LLM (iteration 1): Added proof block to establish contradiction and return 0 as unreachable fallback */
    proof {
        // At this point, we've checked all elements and found none equal to elem
        // But the precondition guarantees that elem exists in the array
        // This creates a contradiction, so this code is unreachable
        assert(forall|j: int| 0 <= j < a.len() ==> a[j] != elem);
        assert(exists|k: int| 0 <= k < a.len() && a[k] == elem);
        assert(false); // contradiction
    }
    
    0 // This line is unreachable due to the contradiction above
}

fn main() {}
}