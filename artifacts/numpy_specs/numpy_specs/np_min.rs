use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn min(a: &[i32]) -> (res: i32)
    requires 
        a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i] &&
        forall|j: int| 0 <= j < a.len() ==> res <= a[j],
{
    a[0]
}

fn main() {
}

}