use vstd::prelude::*;

verus! {

fn ogrid(start: f32, stop: f32, n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures 
        result.len() == n,
        (n == 1 ==> result[0] == start),
        (n > 1 ==> result[0] == start),
        (n > 1 ==> result[n - 1] == stop),
{
    assume(false);
    unreached()
}

}
fn main() {}