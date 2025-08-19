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
        
        let mut res: Vec<u64> = Vec::new();
        let mut i: usize = 0;
          
        while i < a.len()   
        invariant
            a.len() == b.len(),
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == (a[j] & b[j]),
        decreases a.len() - i,
        {
            let val = a[i] & b[i];
            res.push(val);
            i = i + 1;
            assert(i <= a.len());
        }
        assert(i == a.len());
        assert(res.len() == a.len());
        
        res
    }
}