use vstd::prelude::*;

verus! {

#[verifier::external_body] /* TODO: implement */
fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] + b[i],
{
    a.iter().zip(b.iter()).map(|(x, y)| x.wrapping_add(*y)).collect()
}

}

fn main() {}