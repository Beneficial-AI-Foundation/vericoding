
use vstd::prelude::*;

verus! {
    
    fn main() {
       }

    //SPEC
    fn abs(a: Vec<isize>) -> (res: Vec<isize>)
    requires
        forall|i: usize| 0 <= i  < a.len() ==> ( usize::MIN <= #[trigger] a@[i as int] <= usize::MAX),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() && i < res.len() ==> res@[i] as int == (if a@[i] < 0 { -(a@[i]) as int } else { a@[i] as int }),
        forall|i: int| 0 <= i < a.len() && i < res.len() ==> res@[i] as int >= 0
    {
        
        let mut res: Vec<isize> = Vec::new();
        let mut i: usize = 0;
          
        while i < a.len()   
        invariant 
            forall|j: int| 0 <= j < a.len() ==> (usize::MIN <= #[trigger] a@[j] <= usize::MAX),
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res@[j] as int == (if a@[j] < 0 { -(a@[j]) as int } else { a@[j] as int }),
            forall|j: int| 0 <= j < i ==> res@[j] as int >= 0,
        decreases a.len() - i,
        {
            let val = if a[i] < 0 { -(a[i]) } else { a[i] };
            res.push(val);
            i = i + 1;
        }
        
        res
    }
}