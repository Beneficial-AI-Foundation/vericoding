use vstd::prelude::*;

verus! {

// ATOM 
spec fn acheck(a: &[int], n: int) -> bool
    recommends n >= 1
{
    a.len() % 2 == 0 && 
    forall|i: int| 0 <= i < a.len() ==> 
        if i % n == 0 { a[i as usize] == 0 } else { a[i as usize] != 0 }
}

// SPEC 

pub fn Main()
{
}

}