use vstd::prelude::*;

verus! {

fn fmin(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> #[trigger] result[i] == x[i] || #[trigger] result[i] == y[i]
{
    assume(false);
    unreached();
}

}
fn main() {}