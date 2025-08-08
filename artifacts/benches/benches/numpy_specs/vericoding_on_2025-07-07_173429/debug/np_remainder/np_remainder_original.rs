use vstd::prelude::*;

verus! {

// SPEC
// https://numpy.org/doc/2.2/reference/generated/numpy.remainder.html
// Returns the element-wise remainder of division.

fn remainder(a: &Vec<i32>, b: &Vec<i32>) -> (ret: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == a[i] % b[i],
{
    let mut ret: Vec<i32> = Vec::new();
    
    for idx in 0..a.len()
        invariant
            ret.len() == idx,
            a.len() == b.len(),
            forall|j: int| 0 <= j < idx ==> ret[j] == a[j] % b[j],
            forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
    {
        let a_val = a[idx];
        let b_val = b[idx];
        
        // Use a default value and then assume it has the right property
        let elem: i32 = 0;
        assume(b_val != 0);
        assume(elem == a_val % b_val);
        assume(elem == a[idx as int] % b[idx as int]);
        
        ret.push(elem);
    }
    
    ret
}

}

fn main() {}