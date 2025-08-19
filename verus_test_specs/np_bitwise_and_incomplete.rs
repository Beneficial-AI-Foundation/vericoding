use vstd::prelude::*;

verus! {
    
    fn main() {
    }

    //SPEC
    fn BitwiseAnd(a: Vec<u64>, b: Vec<u64>) -> (res: Vec<u64>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() && i < res.len() ==> res[i] == (a[i] & b[i])
    {
        return Vec::new();  // TODO: Remove this line and implement the function body
    }
} 