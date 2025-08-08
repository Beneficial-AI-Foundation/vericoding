use vstd::prelude::*;

verus! {

fn min(a: &[i32]) -> (res: i32)
    requires a.len() > 0
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i],
        forall|i: int| 0 <= i < a.len() ==> res <= a[i]
{
    let mut res = a[0];
    let mut j: usize = 1;
    
    while j < a.len()
        invariant
            1 <= j <= a.len(),
            exists|i: int| 0 <= i < j && res == a[i],
            forall|i: int| 0 <= i < j ==> res <= a[i],
        decreases a.len() - j
    {
        if a[j] < res {
            res = a[j];
        }
        j = j + 1;
    }
    
    res
}

}

fn main() {
    // Empty main function for compilation
}