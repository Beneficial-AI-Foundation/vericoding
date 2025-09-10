use vstd::prelude::*;

verus! {

fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
{
    assume(false);
    unreached();
}

}
fn main() {}