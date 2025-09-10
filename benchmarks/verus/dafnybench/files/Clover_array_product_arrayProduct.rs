use vstd::prelude::*;

verus! {

fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
{
    assume(false);
    unreached()
}

}
fn main() {}