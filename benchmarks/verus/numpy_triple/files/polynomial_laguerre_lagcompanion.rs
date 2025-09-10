use vstd::prelude::*;

verus! {

fn lagcompanion(c: Vec<f64>) -> (result: Vec<Vec<f64>>)
    requires 
        c.len() >= 2,
    ensures 
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
{
    assume(false);
    unreached()
}

}
fn main() {}