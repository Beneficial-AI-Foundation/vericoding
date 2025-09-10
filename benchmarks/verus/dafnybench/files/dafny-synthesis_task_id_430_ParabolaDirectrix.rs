use vstd::prelude::*;

verus! {

fn parabola_directrix(a: int, h: int, k: int) -> (directrix: int)
    requires a != 0
{
    assume(false);
    unreached();
}

}
fn main() {}