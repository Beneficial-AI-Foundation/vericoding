use vstd::prelude::*;

verus! {

fn chebpts2(n: usize) -> (result: Vec<f32>)
    requires n >= 2,
    ensures
        result.len() == n,

        result[0] == -1.0f32,

        result[(n-1) as int] == 1.0f32,
{
    assume(false);
    unreached()
}

}
fn main() {}