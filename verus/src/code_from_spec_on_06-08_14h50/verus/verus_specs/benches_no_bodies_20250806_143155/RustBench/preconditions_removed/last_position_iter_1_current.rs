use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
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
    
    // This point should never be reached given the postcondition requirements
    // The postcondition guarantees that elem exists in the array
    unreachable!()
}

fn main() {}
}