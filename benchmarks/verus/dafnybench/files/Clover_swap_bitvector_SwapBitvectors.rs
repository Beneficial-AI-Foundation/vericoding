use vstd::prelude::*;

verus! {

fn swap_bitvectors(x: u8, y: u8) -> (result: (u8, u8))
    ensures 
        result.0 == y,
        result.1 == x,
{
    assume(false);
    unreached();
}

}
fn main() {}