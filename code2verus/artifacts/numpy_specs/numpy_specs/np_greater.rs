use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn greater(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == (a@[i] > b@[i]),
{
    Vec::new()
}

}

fn main() {}