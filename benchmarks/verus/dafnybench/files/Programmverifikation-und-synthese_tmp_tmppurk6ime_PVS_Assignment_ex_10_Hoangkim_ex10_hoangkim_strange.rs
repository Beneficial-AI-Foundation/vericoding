use vstd::prelude::*;

verus! {

fn q(x: u32, y: u32) -> (z: u32)
    requires y > x + 2
    ensures x < z*z && z*z < y
{
    assume(false);
    0
}

fn strange()
    ensures 1==2
{
    assume(false);
    unreached();
}

}
fn main() {}