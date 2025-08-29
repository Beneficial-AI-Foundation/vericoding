use vstd::prelude::*;

verus! {

fn max(a: &[i32]) -> (res: i32)
    requires 
        a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i],
        forall|i: int| 0 <= i < a.len() ==> a[i] <= res,
{
    // Specification only - no implementation
    assume(false);
    0
}

fn main() {}

}