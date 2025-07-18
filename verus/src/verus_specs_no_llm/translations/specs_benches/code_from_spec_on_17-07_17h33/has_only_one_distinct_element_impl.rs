use vstd::prelude::*;

verus! {

//IMPL has_only_one_distinct_element
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    /* code modified by LLM (iteration 1): moved ensures clause to correct position before function body */
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
{
    if a.len() <= 1 {
        return true;
    }
    
    let first = a[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == first,
        decreases a.len() - i
    {
        if a[i] != first {
            return false;
        }
        i += 1;
    }
    
    true
}

fn main() {}
}