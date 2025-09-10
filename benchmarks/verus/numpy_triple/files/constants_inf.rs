use vstd::prelude::*;

verus! {

fn inf() -> (result: f32)
{
    assume(false);
    unreached();
}

}
fn main() {}