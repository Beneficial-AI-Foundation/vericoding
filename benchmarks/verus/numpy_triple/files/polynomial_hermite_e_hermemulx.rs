use vstd::prelude::*;

verus! {

fn hermemulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() >= 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0,
        forall|i: int| 1 <= i < c.len() ==> result[i + 1] == c[i],
{
    assume(false);
    unreached();
}

}
fn main() {}