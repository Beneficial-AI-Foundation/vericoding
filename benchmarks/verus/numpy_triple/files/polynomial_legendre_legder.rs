use vstd::prelude::*;

verus! {

fn legder(c: Vec<f64>, m: usize, scl: f64) -> (result: Vec<f64>)
    requires c.len() >= 1,
    ensures
        result.len() == if c.len() > m { c.len() - m } else { 1 },
        m == 0 ==> (result.len() == c.len() && forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        m >= c.len() ==> result.len() == 1,
{
    assume(false);
    unreached();
}

}
fn main() {}