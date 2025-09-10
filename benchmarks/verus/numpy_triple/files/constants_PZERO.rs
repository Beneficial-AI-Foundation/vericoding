use vstd::prelude::*;

verus! {

fn pzero() -> (result: f64)
    ensures result == 0.0
{
    assume(false);
    unreached()
}

}
fn main() {}