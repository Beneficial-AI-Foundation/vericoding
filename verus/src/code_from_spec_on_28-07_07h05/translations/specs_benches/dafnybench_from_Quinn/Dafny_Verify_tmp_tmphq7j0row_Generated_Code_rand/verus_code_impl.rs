use vstd::prelude::*;

verus! {
    //IMPL main_method
    fn main_method(x_init: u32, y: u32) -> (z: u32)
        requires 
            (x_init as int) * (y as int) <= u32::MAX as int,
        ensures z == 0
    {
        0
    }
}

fn main() {}