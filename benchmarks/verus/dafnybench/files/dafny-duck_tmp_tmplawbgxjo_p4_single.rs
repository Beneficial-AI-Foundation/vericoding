use vstd::prelude::*;

verus! {

fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
{
    assume(false);
    unreached();
}

}
fn main() {}