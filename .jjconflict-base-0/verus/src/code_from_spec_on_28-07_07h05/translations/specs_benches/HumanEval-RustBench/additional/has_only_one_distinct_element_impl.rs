use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
    // post-conditions-end
{
    if a.len() == 0 {
        return true;
    }
    
    let first_element = a[0];
    let mut i: usize = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == first_element,
        decreases a.len() - i
    {
        if a[i] != first_element {
            return false;
        }
        i += 1;
    }
    
    return true;
}

fn main() {}
}