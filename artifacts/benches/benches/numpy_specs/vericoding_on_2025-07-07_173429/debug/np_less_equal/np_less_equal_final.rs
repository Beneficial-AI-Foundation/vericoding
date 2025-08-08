use vstd::prelude::*;

verus! {

fn less_equal(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (a[i] <= b[i]),
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> res[j] == (a[j] <= b[j]),
        decreases a.len() - i,
    {
        res.push(a[i] <= b[i]);
        i = i + 1;
    }
    
    res
}

}

fn main() {}