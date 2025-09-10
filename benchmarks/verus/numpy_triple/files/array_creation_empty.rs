use vstd::prelude::*;

verus! {

fn empty(n: usize) -> (result: Vec<f32>)
    ensures 
        result.len() == n,
        forall|i: int| 0 <= i < n ==> exists|v: f32| result[i] == v
{
    assume(false);
    unreached()
}

}
fn main() {}