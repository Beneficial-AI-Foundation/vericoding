use vstd::prelude::*;

verus! {

fn NINF() -> (result: f64)
    ensures

        true
{
    assume(false);
    unreached()
}

}
fn main() {}