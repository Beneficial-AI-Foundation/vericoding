use vstd::prelude::*;

verus! {

fn lagpow(c: Vec<f32>, pow: usize, maxpower: usize) -> (result: Vec<f32>)
    requires 
        pow > 0,
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures 
        result.len() == c.len(),
        pow == 1 ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == c[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}