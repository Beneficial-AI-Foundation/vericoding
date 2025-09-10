use vstd::prelude::*;

verus! {

fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
{
    assume(false);
    unreached();
}

}
fn main() {}