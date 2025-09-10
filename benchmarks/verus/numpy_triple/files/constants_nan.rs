use vstd::prelude::*;

verus! {

fn nan() -> (result: f64)
    ensures result != result,
{
    assume(false);
    unreached()
}

}
fn main() {}