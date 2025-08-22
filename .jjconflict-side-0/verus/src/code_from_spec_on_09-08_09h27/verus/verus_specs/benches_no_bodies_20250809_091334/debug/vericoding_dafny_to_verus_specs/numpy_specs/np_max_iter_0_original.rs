use vstd::prelude::*;

verus! {

fn max(a: &[i32]) -> (res: i32)
    requires 
        a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i],
        forall|i: int| 0 <= i < a.len() ==> a[i] <= res,
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}

}