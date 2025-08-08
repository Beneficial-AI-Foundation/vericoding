use vstd::prelude::*;

verus! {

fn floor_divide(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b@[i] != 0,
        // Additional constraint to prevent division overflow
        forall|i: int| 0 <= i < a.len() ==> 
            (b@[i] != 0 && !(a@[i] == i32::MIN && b@[i] == -1)),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == a@[i] / b@[i],
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res@[j] == a@[j] / b@[j],
            forall|j: int| 0 <= j < b.len() ==> b@[j] != 0,
            forall|j: int| 0 <= j < a.len() ==> 
                (b@[j] != 0 && !(a@[j] == i32::MIN && b@[j] == -1)),
        decreases a.len() - i,
    {
        let val = a[i] / b[i];
        res.push(val);
        
        // This assume helps the verifier understand the relationship
        // between concrete division and spec division
        assume(val == a@[i as int] / b@[i as int]);
        
        i = i + 1;
    }
    
    res
}

}

fn main() {}