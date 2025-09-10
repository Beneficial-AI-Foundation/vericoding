use vstd::prelude::*;

verus! {

fn chebmulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
{
    assume(false);
    unreached()
}

}
fn main() {}