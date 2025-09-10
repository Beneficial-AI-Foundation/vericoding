use vstd::prelude::*;

verus! {

fn triangular_prism_volume(base: u32, height: u32, length: u32) -> (volume: u32)
    requires 
        base > 0,
        height > 0,
        length > 0,
    ensures volume == (base * height * length) / 2,
{
    assume(false);
    unreached()
}

}
fn main() {}