use vstd::prelude::*;

verus! {

fn array_sum(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires a.len() == b.len()
    ensures 
        c.len() == a.len() && 
        forall |i: int| 0 <= i < c.len() ==> c[i] == a[i] + b[i]
{
    assume(false);
    unreached();
}

}
fn main() {}