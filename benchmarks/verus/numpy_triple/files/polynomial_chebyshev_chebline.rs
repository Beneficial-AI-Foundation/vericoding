use vstd::prelude::*;

verus! {

fn chebline(off: f32, scl: f32) -> (result: [f32; 2])
    ensures 
        result[0] == off,
        result[1] == scl
{
    assume(false);
    unreached();
}

}
fn main() {}