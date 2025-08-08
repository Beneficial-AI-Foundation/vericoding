use vstd::prelude::*;

verus! {

// IMPL
// https://numpy.org/doc/2.2/reference/generated/numpy.remainder.html
// Returns the element-wise remainder of division.

fn remainder(a: Vec<i32>, b: Vec<i32>) -> (ret: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b@[i] != 0,
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret@[i] == a@[i] % b@[i],
{
    let mut ret = Vec::<i32>::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> ret@[j] == a@[j] % b@[j],
        decreases a.len() - i,
    {
        ret.push(a[i] % b[i]);
        i = i + 1;
    }
    
    ret
}

}

fn main() {}