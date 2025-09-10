use vstd::prelude::*;

verus! {

fn concat(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == b.len() + a.len(),
        forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> c[k + a.len()] == b[k],
{
    assume(false);
    unreached()
}

}
fn main() {}