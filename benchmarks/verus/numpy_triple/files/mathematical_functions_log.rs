use vstd::prelude::*;

verus! {

fn log(x: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i as int] > 0,
    ensures 
        result.len() == x.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}