use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn left_shift(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 16,
        forall|i: int| 0 <= i < a.len() ==> a[i] < (1u16 as i32),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == ((a[i] as u16) << (b[i] as u16)) as i32,
{
    Vec::new()
}

}

fn main() {}