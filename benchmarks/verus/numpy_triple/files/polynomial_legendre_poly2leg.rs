use vstd::prelude::*;

verus! {

fn poly2leg(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == pol.len(),
        forall|i: int| 0 <= i < result.len() ==> exists|c: f32| result[i] == c
{
    assume(false);
    unreached()
}

}
fn main() {}