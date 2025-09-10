use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;

fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x[i])
        }
{
    assume(false);
    unreached();
}

}
fn main() {}