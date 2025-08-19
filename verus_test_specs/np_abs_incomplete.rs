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
        unimplemented!();  // TODO: Remove this line and implement the function body
    }
} 