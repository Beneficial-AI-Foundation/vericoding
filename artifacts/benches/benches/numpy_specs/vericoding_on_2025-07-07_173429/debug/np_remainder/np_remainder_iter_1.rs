use vstd::prelude::*;

verus! {

// Returns the element-wise remainder of division.
fn remainder(a: Vec<i32>, b: Vec<i32>) -> (ret: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == a[i] % b[i],
{
    let mut ret: Vec<i32> = Vec::new();
    let mut i = 0usize;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            a.len() == b.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i@ ==> ret[j] == a[j] % b[j],
        decreases a.len() - i,
    {
        ret.push(a[i] % b[i]);
        i = i + 1;
    }
    ret
}

}

fn main() {}