// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn shares_memory(a: Vec<i8>, b: Vec<i8>) -> bool
{

    true &&

    (a.len() == b.len() && a@ == b@) &&

    true &&

    true
}

fn shares_memory_fn(a: Vec<i8>, b: Vec<i8>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (a.len() == b.len() && a@ == b@ ==> result == true) &&

        true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    if a.len() != b.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() ==> a@[j] == b@[j]);
    assert(a@ =~= b@);
    
    true
}
// </vc-code>

}
fn main() {}