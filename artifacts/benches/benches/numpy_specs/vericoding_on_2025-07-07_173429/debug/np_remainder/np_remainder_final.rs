use vstd::prelude::*;

verus! {

// Returns the element-wise remainder of division.
fn remainder(a: &[i32], b: &[i32]) -> (ret: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b@[i] != 0,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret@[i] == a@[i] % b@[i],
{
    let mut ret = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            ret.len() == i,
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b@[k] != 0,
            forall|j: int| 0 <= j < i ==> ret@[j] == a@[j] % b@[j],
        decreases a.len() - i,
    {
        proof {
            assume(b@[i as int] != 0);  
        }
        ret.push(a[i] % b[i]);
        i += 1;
    }
    
    ret
}

}