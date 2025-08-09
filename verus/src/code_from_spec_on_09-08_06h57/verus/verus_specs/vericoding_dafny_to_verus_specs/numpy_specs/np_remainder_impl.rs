use vstd::prelude::*;

verus! {

// SPEC
// https://numpy.org/doc/2.2/reference/generated/numpy.remainder.html
// Returns the element-wise remainder of division.

fn remainder(a: Vec<i32>, b: Vec<i32>) -> (ret: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == a[i] % b[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        let remainder_val = a[i] % b[i];
        result.push(remainder_val);
        i += 1;
    }
    
    result
}

}

fn main() {}