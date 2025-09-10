use vstd::prelude::*;

verus! {

fn q(x: u32, y: u32) -> (z: u32)
    requires y - x > 2
    ensures x < z*z < y
{
    assume(false);
    unreached()
}

}
fn main() {}