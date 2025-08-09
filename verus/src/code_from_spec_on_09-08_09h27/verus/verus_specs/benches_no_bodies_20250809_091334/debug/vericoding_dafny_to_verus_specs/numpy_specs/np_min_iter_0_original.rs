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
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

}